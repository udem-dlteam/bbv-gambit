(define __bfs_bundle
    (let ()
        (declare
            (standard-bindings)
            (fixnum)
            (block)
            (not safe))
        (define infinity (expt 2 60))

        (define (make-queue) (cons '() '()))
        (define (queue-empty? queue) (null? (car queue)))
        (define (queue-get! queue)
        (let ((x (caar queue)))
            (set-car! queue (cdar queue))
            (if (queue-empty? queue) (set-cdr! queue '()))
            x))
        (define (queue-put! queue x)
        (let ((entry (cons x '())))
            (if (queue-empty? queue)
            (set-car! queue entry)
            (set-cdr! (cdr queue) entry))
            (set-cdr! queue entry)
            x))
        (define (queue-peek queue) (if (queue-empty? queue) #f (caar queue)))

        (define (make-set) (make-table))
        (define (set-add! set x) (table-set! set x #t))
        (define (set-remove! set x) (table-set! set x))
        (define (set-contains? set x) (table-ref set x #f))
        (define (set-length set) (table-length set))
        (define (set-empty? set) (= (set-length set) 0))
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

        ;; all access methods are written such that adding an edge will never delete
        ;; another edge. However, it can make a node dirty
        (define (add-friend! tree node friend)
        (set-add! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
        (set-add! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
        (define (remove-friend! tree node friend)
        (set-remove! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
        (set-remove! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
        (define (get-parent tree x)
        (table-ref (BFSTree-parents tree) x #f))
        (define (set-parent! tree child parent)
        ;; change old parent status to friend
        (let ((old-parent (get-parent tree child)))
            (when old-parent
            (add-friend! tree old-parent child)
            (remove-child! tree old-parent child)))
        ;; if new parent was a friend remove this status
        (remove-friend! tree parent child)
        ;; set parent for child
        (table-set! (BFSTree-parents tree) child parent)
        ;; add child to new parent
        (set-add! (table-ref-or-set-default! (BFSTree-children tree) parent) child))
        (define (remove-parent! tree child)
        (let ((parent (get-parent tree child)))
            (if parent (remove-child! tree parent child)))
        (table-set! (BFSTree-parents tree) child))
        (define (remove-child! tree parent child)
        (set-remove!
            (table-ref (BFSTree-children tree) parent)
            child))

        (define (clean-edge? tree from to)
        (>= (get-rank tree from) (- (get-rank tree to) 1)))
        (define (dirty-edge? tree from to)
        (not (clean-edge? tree from to)))
        (define (edge-exists? tree from to)
        (or (parent? tree to from) (friend? tree from to)))

        (define (children-for-each f tree x)
        (set-for-each f (table-ref-or-set-default! (BFSTree-children tree) x)))
        (define (friends-for-each f tree x)
        (set-for-each f (table-ref-or-set-default! (BFSTree-friends tree) x)))
        (define (neighbors-for-each f tree x)
        (friends-for-each f tree x)
        (children-for-each f tree x))
        (define (friendlies-for-each f tree x)
        (set-for-each f (table-ref-or-set-default! (BFSTree-friendlies tree) x)))
        (define (friendlies->list tree x)
            (set->list (table-ref-or-set-default! (BFSTree-friendlies tree) x)))
            
        (define (source? tree x)
        (= (BFSTree-source tree) x))
        (define (parent? tree x p)
        (eq? p (get-parent tree x)))
        (define (friend? tree x f)
        (set-contains? (table-ref-or-set-default! (BFSTree-friends tree) x) f))

        (define (add-edge! tree from to #!optional onrevive)
            (define queue (make-queue))

            (define (hoist hoister node)
                (when (dirty-edge? tree hoister node)
                (set-parent! tree node hoister)
                (if (and onrevive (= (get-rank tree node) infinity)) (onrevive node))
                (update-rank! tree node)
                (neighbors-for-each
                    (lambda (n)
                    (queue-put! queue node)
                    (queue-put! queue n))
                    tree
                    node)))

            (when (not (edge-exists? tree from to)) ;; no duplicate edges
                (add-friend! tree from to)
                (hoist from to)
                (do () ((queue-empty? queue))
                (hoist (queue-get! queue) (queue-get! queue)))))

        (define (remove-edge! tree from to #!optional onkill)
            (cond
                ((not (parent? tree to from)) ;; edge not in BFS, can be removed safely
                (remove-friend! tree from to))
                (else
                (remove-parent-edge! tree to onkill))))

        (define (remove-parent-edge! tree to #!optional onkill)
            (define loose-queue (make-queue))
            (define catch-queue (make-queue))
            (define loose-set (make-set))
            (define anchor-table (make-table))
            (define all-loosened (make-set))
            (define minimal-loose-rank (get-rank tree to))

            (define (loosen! node)
                (let* ((rank (get-rank tree node))
                    (bucket (table-ref anchor-table rank #f)))
                (when bucket
                    (set-remove! bucket node)
                    (if (set-empty? bucket) (table-set! anchor-table rank)))
                (set-add! all-loosened node)
                (set-rank! tree node infinity)))
            (define (loose? node) (= (get-rank tree node) infinity))

            (define (anchor! node)
                (let* ((rank (get-rank tree node))
                    (bucket (table-ref-or-set-default! anchor-table rank)))
                (set-add! bucket node)))
            (define (anchored? node)
                (let* ((rank (get-rank tree node))
                    (bucket (table-ref anchor-table rank #f)))
                (and bucket (set-contains? bucket node))))

            (define (drop node)
                (when (or (eq? node to)
                          (> (get-rank tree node) minimal-loose-rank))
                    (loosen! node)

                    ;; DFS across subtree to find loose nodes
                    (children-for-each
                    (lambda (child) (if (not (loose? child)) (drop child)))
                    tree
                    node)
                    (friendlies-for-each
                    (lambda (friendly)
                        (if (not (loose? friendly)) (anchor! friendly)))
                    tree
                    node)))

            (define (catch node)
                (neighbors-for-each
                (lambda (neighbor)
                    (when (loose? neighbor)
                    (set-parent! tree neighbor node)
                    (set-remove! all-loosened node)
                    (update-rank! tree neighbor)
                    (queue-put! catch-queue neighbor)))
                tree
                node))

            (remove-parent! tree to)
            (drop to)

            (let* ((cmp (lambda (x y) (< (car x) (car y))))
                    (buckets (list-sort cmp (table->list anchor-table))))
                (for-each
                (lambda (bucket)
                    (let ((rank (car bucket))
                        (head (queue-peek catch-queue)))
                    (do ((next head (queue-peek catch-queue)))
                        ((or (not next) (> (get-rank tree next) rank)))
                        (catch (queue-get! catch-queue))))
                    (set-for-each catch (cdr bucket)))
                buckets)
                ;; all buckets caught, catch rest of the queue
                (do () ((queue-empty? catch-queue))
                (catch (queue-get! catch-queue)))
                (if onkill (set-for-each onkill all-loosened))))

        (define (connected? tree node)
            (not (= (get-rank tree node) infinity)))

        (define (replace! tree node other revive kill)
            (let ((parent (get-parent tree node))
                  (friendlies (friendlies->list tree node)))
                ;; remove all incoming edges to make sure the node is
                ;; not reconnected in the process of adding edges later
                (for-each
                    (lambda (f) (remove-edge! tree f node kill))
                    friendlies)
                (if parent (remove-edge! tree parent node kill))
                (if parent (add-edge! tree parent other revive))
                (for-each
                    (lambda (f) (add-edge! tree f other revive))
                    friendlies)))
        
        (list make-BFSTree add-edge! remove-edge! connected? replace!)))

(define make-BFSTree (list-ref __bfs_bundle 0))
(define add-edge! (list-ref __bfs_bundle 1))
(define remove-edge! (list-ref __bfs_bundle 2))
(define connected? (list-ref __bfs_bundle 3))
(define replace! (list-ref __bfs_bundle 4))
