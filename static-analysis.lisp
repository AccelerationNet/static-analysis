(cl:defpackage :static-analysis
  (:use :cl :cl-user :iterate)
  (:export #:function-call-graph
           #:->dot
           #:call-graph->dot))

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
              "~&subgraph cluster~a{~%label=\"~a (~a nodes)\"~%"
              (cluster-graphviz-name cluster)
              (cluster-label cluster)
              (length (cluster-nodes cluster)))
      (dolist (node (cluster-nodes cluster))
        (format stream "~a [shape=\"record\",label=\"" (node-graphviz-name node))
        (let ((in-count (length (node-called-from node)))
              (out-count (length (node-calls node))))
        (cond
          ((zerop in-count) (format stream "{~a|<out>~a out}" (node-label node) out-count))
          ((zerop out-count) (format stream "~[~;<in>~a~:;{<in>~:*~a in|~a}~]" in-count (node-label node)))
          ((= 1 in-count) (format stream "{<in>~a|<out>~a out}" (node-label node) out-count))
          (T (format stream "{<in>~a in|~a|<out>~a out}" in-count (node-label node) out-count))
          ))
        (format stream "\"]~%")
        (dolist (n (node-calls node))
          (format edges "~A:out -> ~A:in~%" (node-graphviz-name node)
                  (node-graphviz-name n))))
      (format stream "}~%"))
    (format stream (get-output-stream-string edges)))
  (format stream "~&}~%"))

(defun save-as-svg (path graph &aux (path (merge-pathnames path)))
  (with-open-file (stream path :direction :output :if-exists :supersede)
    (->dot graph stream))
  (sb-ext:run-program "/usr/bin/dot" (list "-Tsvg" "-O" (princ-to-string path)))
  (truename path))

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


(defun asdf-systems (&aux (sys (list)))
  (asdf:map-systems #'(lambda (sy) (push sy sys)))
  sys)


(defvar *syscache* (make-hash-table))
(defgeneric asdf-dependencies (thing)
  (:method ((a asdf:system)) (slot-value a 'asdf::load-dependencies))
  (:method ((a T)) (asdf-dependencies (alexandria:ensure-gethash
                                       a *syscache*
                                       (asdf:find-system a)))))

(defmethod asdf-depends-on-p ((a asdf:system) b)
  (member b (asdf-dependencies a)))

(defun asdf-who-depends (system-keyword)
  "finds out who depends on the given system"
  (remove-if-not #'(lambda (system)
                     (asdf-depends-on-p system system-keyword))
                 (asdf-systems)))

(defmethod keyword-name ((a asdf:system))
  (alexandria:make-keyword (string-upcase (asdf:coerce-name a))))

(defun %asdf-graph (root cluster systems)
  (let ((root-node (or (find root (cluster-nodes cluster) :key #'node-label
                             :test #'string-equal)
                       (first (push (make-node :label (princ-to-string root) :cluster cluster)
                                    (cluster-nodes cluster))))))
    (dolist (parent (asdf-dependencies root))
      (let ((parent-node (%asdf-graph parent cluster systems)))
        (pushnew parent-node (node-calls root-node))
        (pushnew root-node (node-called-from parent-node))))
    root-node))

(defun asdf-graph (roots
                   &aux (cluster (make-cluster :label "ASDF load graph"))
                   (systems (asdf-systems))
                   (roots (alexandria:ensure-list roots)))
  (dolist (root roots)
    (%asdf-graph root cluster systems))
  cluster)