(define infinity +inf.0)

(define (make-queue) (cons '() '()))
(define (queue-empty? queue) (null? (car queue)))
(define (queue-get! queue)
  (if (queue-empty? queue)
    (error "queue-get!, queue is empty")
    (let ((x (caar queue)))
      (set-car! queue (cdar queue))
      (if (queue-empty? queue) (set-cdr! queue '()))
      x)))
(define (queue-put! queue x)
  (let ((entry (cons x '())))
    (if (queue-empty? queue)
      (set-car! queue entry)
      (set-cdr! (cdr queue) entry))
    (set-cdr! queue entry)
    x))

(define (make-set) (make-table))
(define (set-add! set x) (table-set! set x #t))
(define (set-remove! set x) (table-set! set x))
(define (set-contains? set x) (table-ref set x #f))
(define (set-for-each f set) (table-for-each (lambda (k _) (f k)) set))
(define (set-search f set) (table-search (lambda (k _) (f k)) set))
(define (set->list set) (map car (table->list set)))

(define (table-ref-or-set-default! table x)
  (let ((value (table-ref table x #f)))
    (or value
        (let ((default (make-set)))
          (table-set! table x default)
          default))))

(define (make-BFSTree source)
  (vector
    source                                  ;; source
    (list->table (list (cons source 0)))    ;; ranks table
    (make-table)                            ;; parents table
    (make-table)                            ;; children table
    (make-table)                            ;; friends table
    (make-table)))                          ;; friendlies table

(define (BFSTree-source tree) (vector-ref tree 0))
(define (BFSTree-ranks tree) (vector-ref tree 1))
(define (BFSTree-parents tree) (vector-ref tree 2))
(define (BFSTree-children tree) (vector-ref tree 3))
(define (BFSTree-friends tree) (vector-ref tree 4))
(define (BFSTree-friendlies tree) (vector-ref tree 5))

;;   Parent P of X
;;   P -> X where rank(X) = rank(P) + 1
;;
;;     P
;;     |
;;     |
;;     v
;;     X

;;   Child C of X
;;   C if a child of X if X is a parent of C

;;   Friend F of X
;;   X -> F where rank(X) >= rank(F) - 1
;;
;;  F     
;;  ^     
;;  |     P
;;  |     |
;;  \     v
;;   \--- X

(define (get-rank tree x)
  (table-ref (BFSTree-ranks tree) x infinity))
(define (set-rank! tree x rank)
  (table-set! (BFSTree-ranks tree) x rank))
(define (update-rank! tree x)
  (let* ((parent (get-parent tree x))
         (parent-rank (if parent (get-rank tree parent) infinity))
         (old-rank (get-rank tree x))
         (new-rank (+ parent-rank 1)))
    (if (= new-rank old-rank) #f (begin (set-rank! tree x new-rank) #t))))

(define (get-parent tree x)
  (table-ref (BFSTree-parents tree) x #f))
(define (remove-child! tree parent child)
  (set-remove!
    (table-ref (BFSTree-children tree) parent)
    child))
(define (set-parent! tree child parent)
  ;; remove old parent
  (let ((old-parent (get-parent tree child)))
    (if old-parent (remove-child! tree old-parent child)))
  ;; set parent for child
  (table-set! (BFSTree-parents tree) child parent)
  ;; add child to new parent
  (set-add! (table-ref-or-set-default! (BFSTree-children tree) parent) child))
(define (remove-parent! tree child)
  (let ((parent (get-parent tree child)))
    (if parent (remove-child! tree parent child)))
  (table-set! (BFSTree-parents tree) child))
(define (get-children tree x)
  (table-ref-or-set-default! (BFSTree-children tree) x))

(define (add-friend! tree node friend)
  (set-add! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
  (set-add! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
(define (remove-friend! tree node friend)
  (set-remove! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
  (set-remove! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
(define (get-friends tree x)
  (table-ref-or-set-default! (BFSTree-friends tree) x))
(define (get-friendlies tree x)
  (table-ref-or-set-default! (BFSTree-friendlies tree) x))

(define (clean-edge? tree from to)
  (>= (get-rank tree from) (- (get-rank tree to) 1)))
(define (dirty-edge? tree from to)
  (not (clean-edge? tree from to)))

(define (children-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-children tree) x)))
(define (friends-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friends tree) x)))
(define (neighbors-for-each f tree x)
  (friends-for-each f tree x)
  (children-for-each f tree x))
(define (friendlies-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friendlies tree) x)))

(define (get-lowest-ranked-incident-node tree x)
  ;; favor parent in case of tie
  (let* ((best (get-parent tree x))
         (best-rank (if best (get-rank tree best) infinity)))
    (friendlies-for-each
      (lambda (f)
        (let ((rank (get-rank tree f)))
          (when (< rank best-rank)
            (set! best f)
            (set! best-rank rank))))
      tree
      x)
    best))
    

(define (source? tree x)
  (= (BFSTree-source tree) x))
(define (parent? tree x p)
  (eq? p (get-parent tree x)))

(define (add-edge! tree from to)
  (cond
    ((clean-edge? tree from to) ;; adding this edge cannot lower rank
      (add-friend! tree from to))
    (else ;; forward edge may reduce the rank of some nodes
      (let ((dirty-queue (make-queue)))
        (define (hoist new-parent node)
          (let ((old-parent (get-parent tree node)))
            ;; set new parent
            (set-parent! tree node new-parent)
            ;; if node was a friend of new-parent remove the relation
            (remove-friend! tree new-parent node)
            ;; the old parent now has rank higher or equal to node
            ;; node is now a friend of the old parent
            (if old-parent (add-friend! tree old-parent node))
            ;; recompute the rank with this new parent
            (if (update-rank! tree node)
              ;; if rank changed
              ;; Search for edges that are now higher ranked
              ;; and mark them as dirty to be fixed later
              (neighbors-for-each
                (lambda (x)
                  (when (dirty-edge? tree node x)
                    (queue-put! dirty-queue (list node x))))
                tree
                node))))

        (queue-put! dirty-queue (list from to))

        (let loop ()
          (when (not (queue-empty? dirty-queue))
            (apply hoist (queue-get! dirty-queue))
            (loop)))))))

(define (remove-edge! tree from to)
  (cond
    ((not (parent? tree to from)) ;; edge not in BFS, can be removed safely
      (remove-friend! tree from to))
    (else
      (let ((dirty-queue (make-queue)))
        (define (drop node)
          ;; dirty node rank, parent and friendlies may not match
          (let ((new-parent (get-lowest-ranked-incident-node tree node)))
            (when new-parent
              (remove-friend! tree new-parent node)
              (set-parent! tree node new-parent))

            (if (update-rank! tree node)
              ;; the new parent has higher rank, so we mark children
              ;; to assign them a better parent
              (children-for-each
                (lambda (child)
                  (queue-put! dirty-queue child))
                tree
                node))))

        (remove-parent! tree to)

        (queue-put! dirty-queue to)

        (let loop ()
          (when (not (queue-empty? dirty-queue))
            (drop (queue-get! dirty-queue))
            (loop)))))))

;; tests

(define (test)
  (define tree (make-BFSTree 0))

  ;; make a long chain
  (add-edge! tree 0 1)
  (add-edge! tree 1 2)
  (add-edge! tree 2 3)
  (add-edge! tree 3 4)

  ;; make a diamond segment at the end of the chain
  (add-edge! tree 4 5)
  (add-edge! tree 4 6)
  (add-edge! tree 5 7)
  (add-edge! tree 6 7)

  ;; make a loop
  (add-edge! tree 7 1)

  ;; short-circuit the chain
  (add-edge! tree 0 5)

  (let ((ranks (map (lambda (n) (get-rank tree n)) (iota 8)))
        (expected-ranks '(0 1 2 3 4 1 5 2)))
    (if (equal? ranks expected-ranks)
        (pp 'OK)
        (begin
          (pp 'FAILED)
          (pp ranks))))
        
  (remove-edge! tree 0 5)
  (remove-edge! tree 2 3)
  (pp (map (lambda (n) (get-rank tree n)) (iota 8))))

(test)
