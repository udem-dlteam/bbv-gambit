(define-library (ssr-graph)
  (export
    make-graph
    add-edge!
    remove-edge!
    redirect!
    connected?)
  (import gambit)
  (include "ssr-graph.scm"))
