;; File: process-issue.scm

(define (run n)
  (let loop ((i 0))
    (if (< i n)
        (begin
          (if (= 0 (modulo i 100)) (println "--------- " i))
          (with-exception-catcher
           (lambda (exc)
             (println "*** after " i " iterations got this exception:")
             (display-exception exc))
           (lambda ()
             (call-with-output-process "echo" ##newline)))
          (loop (+ i 1))))))

(run 10000)
