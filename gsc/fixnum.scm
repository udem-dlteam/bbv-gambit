;;;============================================================================

;;; File: "fixnum.scm"

;;; Copyright (c) 1994-2022 by Marc Feeley, All Rights Reserved.

(##declare
  (standard-bindings)
  (fixnum)
  ;(debug) (debug-source) (debug-location) ;; uncomment for profiling with statprof
)

(##define-macro (include-adt filename)
  `(begin
     (##declare (not core))
     (##include ,(string-append "../gsc/" filename))
     (##declare (core))))

;;;============================================================================
