(defsystem :static-analysis
  :description "experimental project for doing static analysis on loaded lisp code."
  :author "Ryan Davis <ryan@acceleration.net>"
  :version "0.0.1"
  :serial T
  :components ((:file "static-analysis"))
  :depends-on (:iterate :alexandria :swank))