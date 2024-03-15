;; requires compilation with (debug) (debug-source) (debug-location)

(define __statprof-bundle
  (let ()
    (##include "~~lib/gambit/prim/prim#.scm") ;; map fx+ to ##fx+, etc
    (##include "~~lib/_gambit#.scm")          ;; for macro-check-string,
                                            ;; macro-absent-obj, etc

    (declare (safe) (generic))          ;; claim code has no type errors

    ;;;============================================================================

    ;; Profiling & interrupt handling

    (define *buckets* #f)
    (define *table-of-frames* #f)
    (define *total* 0)
    (define *profile?* #f)
    (define *flamegraph?* #f)
    (define *busy* #f)

    (define (statprof-start! #!optional (kind '(profile)))
    (set! *profile?* (not (not (member 'profile kind))))
    (set! *flamegraph?* (not (not (member 'flamegraph kind))))
    (set! *buckets* (make-table))
    (set! *table-of-frames* (make-table))
    (set! *total* 0)
    (heartbeat-interrupt-handler-set! statprof-heartbeat!))

    (define (statprof-stop!)
    (heartbeat-interrupt-handler-set! ##thread-heartbeat!))

    (define (heartbeat-interrupt-handler-set! thunk)
    (##interrupt-vector-set! 2 thunk)) ;; 2 = ___INTR_HEARTBEAT

    (define (identify-continuation cont)
    (let loop ((cont cont))
        (and cont
            (let ((locat (##continuation-locat cont)))
            (if locat
                (let* ((container (##locat-container locat))
                        (file (##container->path container)))
                    (if file
                        (let* ((filepos
                                (##position->filepos (##locat-position locat)))
                                (line
                                (fx+ (##filepos-line filepos) 1)))
                        (vector file line))
                        (loop (##continuation-next! cont))))
                (loop (##continuation-next! cont)))))))

    (define (continuation->frames cont)
      (let loop ((cont cont) (lst '()))
        (if (not cont)
            lst
            (if (##interesting-continuation? cont)
                (let ((creator (##continuation-creator cont)))
                  (loop (##continuation-next! cont)
                        (if creator
                            (cons (##procedure-name creator) lst)
                            lst)))
                (loop (##continuation-next! cont)
                      lst)))))

    (define (statprof-heartbeat!)
    (continuation-capture
      (lambda (cont)
        (let ((count 1))
          (if (not *busy*)
            (begin
            (set! *busy* #t)
            (if *profile?*
              (let ((id (identify-continuation cont)))
                  (if id
                      (let* ((file
                              (vector-ref id 0))
                              (bucket
                              (or (table-ref *buckets* file #f)
                                  (let ((b (make-vector 20000 0))) ;; fixme length limit
                                  (table-set! *buckets* file b)
                                  b)))
                              (line
                              (vector-ref id 1)))
                      (if (fx< line (vector-length bucket))
                          (begin
                              (vector-set! bucket
                                          line
                                          (fx+ count (vector-ref bucket line)))
                              (set! *total* (fx+ count *total*))))))))

            (if *flamegraph?*
                (let ((frames (continuation->frames cont)))
                    (table-set! *table-of-frames*
                                frames
                                (fx+ count (table-ref *table-of-frames* frames 0)))))

            (set! *busy* #f)
            (##thread-heartbeat!)))))))

    ;; ----------------------------------------------------------------------------
    ;; Text formatting

    (define (pad-left s l c)
    (let loop ((s (string->list s)))
        (if (< (length s) l)
            (loop (cons c s))
            (list->string s))))


    ;; ----------------------------------------------------------------------------
    ;; Palette generation & color formatting

    (define (gradient from to step)
    (let ((inc (map (lambda (x) (/ x step))
                    (map - to from))))

        (let loop ((i 0)
                (acc '()))
        (if (= i step)
            (reverse acc)
            (loop (+ i 1)
                    (cons (map
                        (lambda (x o)
                            (round (+ x (* i o))))
                        from
                        inc)
                        acc))))))

    (define (as-rgb col)
    (apply string-append
            (map
            (lambda (x)
                (pad-left (number->string x 16) 2 #\0))
            col)))

    (define palette
    (list->vector
    (cons '(255 255 255)
            (gradient '(127 127 255)
                    '(255 127 127)
                    16))))


    ;; ----------------------------------------------------------------------------
    ;; Functions to generate the report

    (define (statprof-write! profile-dir #!optional (context 10))

    (define output-dir (path-expand profile-dir))

    (with-exception-catcher
    (lambda (e)
        ;; ignore the exception, it probably means that the directory
        ;; already existed.  If there's another problem it will be
        ;; signaled later.
        #f)
    (lambda ()
        (create-directory (list path: output-dir
                                permissions: #o755))))

    (if *profile?*
        (profile-write! output-dir context))

    (if *flamegraph?*
        (flamegraph-write! output-dir)))

    (define (profile-write! output-dir context)

    (define buckets (table->list *buckets*))

    (define (generate-result-file-for-bucket bucket max-intensity)
        (let ((file (car bucket))
            (data (vector-copy (cdr bucket))))

        (define (get-color n)
            (let ((i (or (vector-ref data n) 0)))
            (if (= i 0)
                (as-rgb (vector-ref palette 0))
                (let ((x
                        (if (<= max-intensity 1)
                            0
                            (* (/ (log (+ 1. i))
                                (ceiling (log max-intensity)))
                                (- (vector-length palette) 1)))))
                    (as-rgb (vector-ref palette
                                        (inexact->exact (ceiling x))))))))

        (define (remove-out-of-context)
            (let loop ((i (- context))
                    (cont (+ context 1))
                    (start-of-prev-removed #f))

            (define (possibly-undo-prev-remove i)
                (let ((i-1 (- i 1)))
                (if (and start-of-prev-removed
                        (>= i-1 0)
                        (= (max 0 start-of-prev-removed) i-1))
                    (vector-set! data i-1 0))))

            (if (< i (vector-length data))
                (let ((remove? (>= cont context)))
                    (if remove?
                        (if (>= i 0) (vector-set! data i #f))
                        (possibly-undo-prev-remove i))
                    (loop (+ i 1)
                        (let ((j (+ i context 2)))
                            (if (and (< j (vector-length data))
                                    (> (vector-ref data j) 0))
                                (- (+ context 1))
                                (+ cont 1)))
                        (and remove?
                            (or start-of-prev-removed i))))
                (possibly-undo-prev-remove i))))

        (define (generate-table-rows lines)
            (let ((nlines (length lines)))

            (define (ellision)
                `(tr (td) (td) (td "...")))

            (define (row i line)
                (let ((line# (+ i 1)))
                `(tr

                    (td
                    align: right
                    style: "padding-left: 5px; padding-right: 5px"
                    ,(let ((n (or (vector-ref data line#) 0)))
                        (if (= n 0)
                            ""
                            `(strong
                            ,(round% (/ n *total*))))))

                    (td ,(string-append
                        (number->string line#)
                        ": "))
                    ;; (td
                    ;;  align: center
                    ;;  ,(let ((n (vector-ref data line#)))
                    ;;     (if (= n 0)
                    ;;         ""
                    ;;         (string-append "["
                    ;;                        (number->string n)
                    ;;                        "/"
                    ;;                        (number->string *total*)
                    ;;                        "]"))))

                    (td (pre style: ,(string-append
                                    "background-color:#"
                                    (get-color line#))
                            ,line)))))

            (let loop ((i (- nlines 1))
                        (end-of-removed #f)
                        (lst (reverse lines))
                        (rows '()))
                (if (< i 0)
                    rows
                    (if (vector-ref data i)
                        (loop (- i 1)
                            #f
                            (cdr lst)
                            (cons (row i (car lst)) rows))
                        (if end-of-removed
                            (loop (- i 1)
                                end-of-removed
                                (cdr lst)
                                rows)
                            (loop (- i 1)
                                i
                                (cdr lst)
                                (cons (ellision) rows))))))))

        (remove-out-of-context)

        (let ((html
                (sexp->html
                `(html
                    (body
                    (table
                    cellspacing: 0
                    cellpadding: 0
                    border: 0
                    style: "font-size: 12px;"
                    ,@(generate-table-rows
                        (call-with-input-file file
                        (lambda (p) (read-all p read-line))))))))))
        (with-output-to-file (path-expand (string-append
                                            (path-strip-directory file)
                                            ".html")
                                            output-dir)
            (lambda ()
            (print html))))))

    (if (> *total* 0)
        (let ((max-intensity
                (fold max
                    0
                    (map
                        (lambda (data)
                        (fold max 0 (vector->list data)))
                        (map cdr buckets)))))
            (for-each (lambda (bucket)
                        (generate-result-file-for-bucket bucket max-intensity))
                    buckets)))

    (with-output-to-file (path-expand "index.html" output-dir)
        (lambda ()
        (print
        (sexp->html
            `(html
            (body
            ,@(if (= 0 *total*)
                    '("profile is empty")
                    (map (lambda (bucket)
                            (let ((file-path
                                (path-expand
                                    (string-append
                                    (path-strip-directory (car bucket))
                                    ".html")
                                    output-dir)))
                            `(p (a href: ,file-path ,file-path)
                                " ["
                                ,(round%
                                    (/ (fold + 0 (vector->list (cdr bucket)))
                                    *total*))
                                "]")))
                        buckets)))))))))

    (define (round% n)
    (let* ((x
            (number->string (exact (round (* 1000 n)))))
            (y
            (string-append (make-string (max 0 (- 2 (string-length x))) #\0)
                            x))
            (len
            (string-length y)))
        (string-append
        (substring y 0 (- len 1))
        "."
        (substring y (- len 1) len)
        "%")))


    ;; ----------------------------------------------------------------------------
    ;; Included file "html.scm"
    ;; ----------------------------------------------------------------------------

    ;; html.scm -- A simple html generator for Gambit-C 4.0

    ;; Written by Guillaume Germain (germaing@iro.umontreal.ca)
    ;; This code is released in the public domain.


    (define (stringify x)
    (with-output-to-string ""
        (lambda ()
        (print x))))

    (define (to-escaped-string x)
    (stringify
    (map (lambda (c)
            (case c
                ((#\<) "&lt;")
                ((#\>) "&gt;")
                ((#\&) "&amp;")
                (else c)))
            (string->list
            (stringify x)))))

    ;; Quick and dirty conversion of s-expressions to html
    (define (sexp->html exp)

    ;; write the opening tag
    (define (open-tag exp)
        (cond
        ;; null tag isn't valid
        ((null? exp)
        (error "null tag"))

        ;; a tag must be a list beginning with a symbol
        ((and (pair? exp)
            (symbol? (car exp)))
        (list "<"
                (car exp)
                " "
                (maybe-args (car exp) (cdr exp))))

        (else
        (error "invalid tag" exp))))

    ;; take care of the keywords / arguments
    (define (maybe-args tag exp)

        (cond
        ;; does the rest of the list begins with a keyword
        ((and (pair? exp)
            (keyword? (car exp)))

        ;; does the keyword has an associated value?
        (if (or (null? (cdr exp))
                (keyword? (cadr exp)))
            ;; no, we don't put an associated value
            (list (keyword->string (car exp))
                    " "
                    (maybe-args tag (cdr exp)))
            ;; yes, we take the next element in the list as the value
            (list (keyword->string (car exp))
                    "=\""
                    (cadr exp)
                    "\" "
                    (maybe-args tag (cddr exp)))))

        ;; must just be some content
        (else
        (content tag exp))))

    ;; handle the content of the tag and closing it
    (define (content tag exp)
        (cond
        ;; no content...
        ((null? exp)
        ;;(list "></" tag ">"))           ; close as "<br></br>"
        (list "/>"))                      ; close as "<br/>"

        ;; write the content, handle tags inside
        ((pair? exp)
        (list ">"
                (map (lambda (e)
                    (if (pair? e)
                        (open-tag e)
                        (to-escaped-string e)))
                    exp)
                "</"
                tag
                ">"))

        ;; non-null terminated list?
        (else
        (error "strange content..."))))

    ;; we rely on Gambit's flattening of list when printed with print
    (with-output-to-string (lambda ()
                            (print (open-tag exp)))))

    ;; ----------------------------------------------------------------------------

    (define (flamegraph-write! output-dir)

    (define (frames->string lst)
        (string-concatenate (map symbol->string lst) ";"))

    (let ((sorted-frames
            (list-sort
            string<=?
            (map (lambda (x)
                    (string-append (frames->string (car x))
                                    " "
                                    (number->string (cdr x))))
                (table->list *table-of-frames*)))))
        (call-with-output-file
            (path-expand "flamegraph.folded" output-dir)
        (lambda (port)
        (for-each
            (lambda (s)
            (display s port)
            (newline port))
            sorted-frames)))))

  (list statprof-start! statprof-stop! statprof-write!)))

(define statprof-start! (list-ref __statprof-bundle 0))
(define statprof-stop! (list-ref __statprof-bundle 1))
(define statprof-write! (list-ref __statprof-bundle 2))

(define (%statprof-thunk) #f)

(define (statprof-begin)
  (println "statprof is up")
  (if (not (##subprocedure-info %statprof-thunk))
      (println "*** Profiling without debug location."))
  (statprof-start! '(flamegraph profile)))

(define (statprof-end path)
  (let ((profile-dir (path-expand (string-append path ".statprof"))))
    (println "statprof is done")
    (statprof-stop!)
    (statprof-write! profile-dir)))
;;;============================================================================
