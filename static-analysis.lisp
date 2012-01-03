(cl:defpackage :static-analysis
  (:use :cl :cl-user :iterate))

(in-package :static-analysis)

(defun asdf-files (system)
  "generates a list of files in the ASDF system, in load order"
  (rest (swank:asdf-system-files system)))

(defun read-file (path)
  (check-type path pathname)
  (with-open-file (s path)
    (iter
      (for form = (read s nil 'done))
      (until (eq form 'done))
      (collect form))))

(defun callers (symbol)
  (check-type symbol symbol)
  (mapcar #'first
          (or (ignore-errors
               (and (fdefinition symbol)
                    (swank-backend:who-calls symbol)))
              (swank-backend:who-macroexpands symbol))))

(defun ensure-package-list (packages)
  (when packages
    (let ((packages (alexandria:ensure-list packages)))
      (if (every #'packagep packages) packages
          (mapcar #'find-package (alexandria:flatten packages))))))

(defun map-symbols (fn packages &aux (packages (ensure-package-list packages)))
  (check-type fn function)
  (check-type packages list)
  (with-package-iterator (gen packages :internal :external :inherited)
    (with-simple-restart (abort "stop iterating")
      (iter (multiple-value-bind (more? symbol accessibility pkg) (gen)
              (with-simple-restart (continue "skip to the next symbol")
                (funcall fn symbol accessibility pkg))
              (while more?))))))


;; ;; throws compiler error
;; (defun package-iterator (x)
;;   (when (every #'packagep x)
;;       (with-package-iterator (gen x :internal :external :inherited)
;;         (gen))))

(defun orphan-p (symbol)
  (break "~A, callers: ~a, refs: ~a, binds: ~a, sets: ~a, specs: ~a" symbol
         (callers symbol)
         (swank-backend:who-references symbol)
         (swank-backend:who-binds symbol)
         (swank-backend:who-sets symbol)
         (swank-backend:who-specializes symbol)))

(defun check-for-orphans (package)
  (check-type package package)
  (map-symbols #'(lambda (symbol accessibility pkg)
                   (when (orphan-p symbol)
                     (format T "~&~A ~A ~A~%" symbol pkg accessibility))
                   )
               package))

(defstruct (cluster (:print-object cluster-printer))
  label
  (nodes (list))
  (graphviz-name (gensym)))

(defun cluster-printer (cluster stream)
  (print-unreadable-object (cluster stream :type T :identity T)
    (format stream "label: ~a, nodes: ~a" (cluster-label cluster)
            (length (cluster-nodes cluster)))))

(defstruct (node (:print-object node-printer))
  label
  (graphviz-name (gensym))
  (cluster nil)
  (called-from (list))
  (calls (list)))

(defun node-printer (node stream)
  (print-unreadable-object (node stream :type T :identity T)
    (format stream "label: ~a, calls: ~a, called ~a" (node-label node)
            (length (node-calls node))
            (length (node-called-from node)))))

(defun call-graph (packages &aux
                   (packages (ensure-package-list packages))
                   pkgs)
  (labels ((ensure-pkg (sym &aux (pkg (package-name (symbol-package sym))))
             (or
              (find pkg pkgs :test #'string= :key #'cluster-label)
              (first (push (make-cluster :label pkg) pkgs))))
           (ensure-sym (sym &aux (cluster (ensure-pkg sym))
                            (label (symbol-name sym)))
             (or (find label (cluster-nodes cluster)
                       :test #'string= :key #'node-label)
                 (first (push
                  (make-node :label label :cluster cluster)
                  (cluster-nodes cluster)))))
           (edge (sym caller &aux
                      (sym (ensure-sym sym))
                      (caller (ensure-sym caller)))
             (pushnew sym (node-calls caller))
             (pushnew caller (node-called-from sym)))
           (process-sym (symbol accessibility pkg)
             (declare (ignore accessibility pkg))
             (let ((callers (remove-duplicates
                         (mapcar #'(lambda (caller)
                                     ;; something like
                                     ;; (DEFMETHOD fn (args))
                                     (if (listp caller)
                                         (let ((fn (second caller)))
                                           ;; something like (setf foo)
                                           (if (listp fn) (second fn)
                                               fn))
                                         caller))
                                 (callers symbol)))))
               (dolist (c callers)
                 (edge symbol c)))))
    (map-symbols #'process-sym packages))
  pkgs)

(defun ->dot (clusters &optional (stream T)
              &aux (*print-pretty* nil))
  (format stream "~&digraph g{~%")
  (with-open-stream (edges (make-string-output-stream))
    (dolist (cluster clusters)
      (format stream
              "~&subgraph cluster~a{~%label=\"PACKAGE ~a\"~%"
              (cluster-graphviz-name cluster)
              (cluster-label cluster))
      (dolist (node (cluster-nodes cluster))
        (format stream "~a [label=~s]~%"
                (node-graphviz-name node)
                (node-label node))
        (dolist (n (node-calls node))
          (format edges "~A -> ~A~%" (node-graphviz-name node)
                  (node-graphviz-name n))))
      (format stream "}~%"))
    (format stream (get-output-stream-string edges)))
  (format stream "~&}~%"))

(defun call-graph->dot (packages &optional (stream T))
  (->dot (call-graph packages) stream))


(defun function-call-graph (packages symbols &optional (max-depth 1024)
                            &aux nodes-to-keep
                            seen)
  "spiders down from symbols"
  (labels ((add-nodes (node &optional (depth 0))
             (when (and node (< depth max-depth))
               (pushnew node nodes-to-keep)
               (unless (member node seen)
                 (push node seen)
                 (dolist (n (node-calls node))
                   (add-nodes n (1+ depth)))))))
    (iter
      (with call-graph = (call-graph packages))
      (for sym in symbols)
      (for cluster = (find (package-name (symbol-package sym))
                           call-graph
                           :test #'string= :key #'cluster-label))
      (for node = (find (symbol-name sym)
                        (cluster-nodes cluster)
                        :test #'string= :key #'node-label))
      (add-nodes node)
      ))
  (iter (for n in nodes-to-keep)
    (setf (node-calls n)
          (intersection (node-calls n)
                        nodes-to-keep)))
  (iter
    (for cluster in (remove-duplicates (mapcar #'node-cluster nodes-to-keep)))
    (collect
        (make-cluster :label (cluster-label cluster)
                      :nodes (remove-if-not #'(lambda (node)
                                                (eq cluster (node-cluster node)))
                                        nodes-to-keep)))))