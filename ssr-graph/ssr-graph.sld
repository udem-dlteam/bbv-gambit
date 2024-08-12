(define-library (ssr-graph)
  (export
    make-graph
    add-edge!
    remove-edge!
    redirect!
    redirect-many!
    connected?)
  (import gambit)
  (include "ssr-graph.scm"))
