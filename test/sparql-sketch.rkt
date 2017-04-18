#lang rosette

(define _ '_)

(current-bitwidth #f)

(define uris '(uri1 uri2 uri3 uri4 uri5 uri6 uri7))

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(define values (append '("Rob" "Robert" "Jon" "Jonathon" "Paula" "Allison") (list S1 S2)))

(define all-atoms (append uris values))

(require ocelot)
(require rosette/lib/synthax)

(define U (universe all-atoms))

(define triples (declare-relation 3 "Triples"))

(define triples-bound
  (make-exact-bound
   triples
   '((uri1 uri5 "Robert")
     (uri2 uri5 "Jonathon")
     (uri3 uri5 "Paula")
     (uri4 uri5 "Allison")
     (uri6 uri7 uri1)
     (uri6 uri7 uri3))))

(define yes-triples (declare-relation 3 "Triples"))

(define yes-triples-bound
  (make-exact-bound
   yes-triples
   '((uri1 uri5 "Rob")
     (uri2 uri5 "Jon"))))

(define no-triples (declare-relation 3 "NoTriples"))

(define no-triples-bound
  (make-exact-bound
   no-triples
   '((uri3 uri5 "Paula"))))


(define entities (declare-relation 1 "URIs"))

(define entities-bound (make-exact-bound entities (map list uris)))

(define literals (declare-relation 1 "Literals"))

(define literals-bound (make-exact-bound literals (map list values)))

(define atoms (declare-relation 1 "Atoms"))

(define atoms-bound (make-exact-bound atoms (map list all-atoms)))

(define answers (declare-relation 2 "Map"))

(define answers-bound (make-product-bound answers uris all-atoms))

(define atom-relations (make-hash (map (lambda (a) (cons a (declare-relation 1 a))) all-atoms)))

(define atom-bounds (hash-map atom-relations (lambda (k v) (make-exact-bound v (list (list k))))))

(define (is-atom? a)
  (hash-has-key? atom-relations a))

(define limits (bounds U (append atom-bounds (list literals-bound entities-bound answers-bound atoms-bound triples-bound yes-triples-bound no-triples-bound))))

(define ib (instantiate-bounds limits))

(define (solve-it x)
  (time
   (begin
     (solver-clear (current-solver))
     (solver-assert (current-solver) (list (interpret* x ib)))
     (solver-check (current-solver)))))

;;

(define (triple s p v)
  (if (or (is-atom? s) (eq? s _))
      (let ((rel (if (eq? s _) entities (hash-ref atom-relations s))))
        (some ([x rel])
              (triple x p v)))
      (if (or (is-atom? p) (eq? p _))
          (let ((rel (if (eq? p _) entities (hash-ref atom-relations p))))
            (some ([x rel])
                  (triple s x v)))
          (if (or (is-atom? v) (eq? v _))
              (let ((rel (if (eq? v _) atoms (hash-ref atom-relations v))))
                (some ([x rel])
                      (triple s p x)))
              (in (-> s p v) triples)))))

;;

(define ex1
  (let ((model
         (solve-it
          (and
           (all ([s (join answers literals)])
                (some (join s (join triples literals))))
           (all ([s (join (join triples literals) entities)])
                (and
                 (one (join s answers))
                 (all ([v (join atoms (join s triples))])
                      (in v (join s answers)))))))))
    (interpretation->relations (evaluate ib model) model)))

(define ex2
  (let ((model
         (solve-it
            (and
             (all ([s (join answers literals)])
                  (some (join s (join triples literals))))
             (all ([s (join (join triples literals) entities)])
                  (and
                   (one (join s answers))
                   (all ([v (join entities (join s triples))])
                        (is-string-prefix? (join s answers) v))))))))
      (interpretation->relations (evaluate ib model) model)))

(define ex3
  (let ((model
         (solve-it
          (and
           (= (join (join triples literals) entities) (join answers literals))
           (=
            answers
            (set ([s entities] [nn literals])
                 (some ([p entities] [n literals])
                       (and (apply-predicate
                             (lambda (x y)
                               (and (string? x)
                                    (string? y)
                                    (> (string-length y) 0)
                                    (> (string-length x) (string-length y))
                                    (string-prefix? x y)))
                             n nn)
                            (in (-> s p n) triples)))))))))
      (interpretation->relations (evaluate ib model) model)))

(define ex4
  (let ((m
         (solve-it
          (=
           answers
           (set ([s entities] [nn literals])
                (some ([p entities] [n literals])
                      (and (is-string-prefix? nn n)
                           (in (-> s p n) triples))))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex5
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (some ([t entities])
                        (and
                         (some ([p1 entities])
                               (in (-> s p1 t) triples))
                         (some ([p2 entities])
                               (in (-> t p2 v) triples)))))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex6
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (and
                   (some ([p entities])
                         (triple s p v))
                   (apply-predicate
                    (lambda (s)
                      (and (string? s)
                           (< (string-length s) 7)))
                    v)))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex7
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (triple s 'uri5 v))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex8
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (and
                   (triple _ _ s)
                   (triple s 'uri5 v)))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex9
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (and
                   (apply-predicate
                    (lambda (s)
                      (and (string? s) (> (string-length s) 6)))
                    v)
                   (triple s 'uri5 v)))))))
    (interpretation->relations (evaluate ib m) m)))




(define-symbolic i1 integer?)

(define (iop i) (and ([choose > = <] i i1) (< 0 i1)))



(define ex10
  (let ((m (solve-it
           (and
             (= answers (set ([s entities] [v literals])
               (and (apply-predicate (lambda (ss) (and (string? ss) (iop (string-length ss)))) v)
                    (triple s 'uri5 v))))
             
             (all ([s (join (join yes-triples literals) entities)])
              (and (some (join s answers))
                   (all ([v (join atoms (join s yes-triples))]) (in v (join s answers)))))
             
             (all ([s (join (join no-triples literals) entities)])
              (all ([v (join atoms (join s no-triples))]) (not (in v (join s answers)))))
            )
         )))
     (assert (<= i1 (apply max (map (lambda (t) (string-length (car t)))
                                    (hash-ref (interpretation->relations (evaluate ib m) m) literals)))))
     (print-forms m)
     (println (evaluate i1 m))
     (println (interpretation->relations (evaluate ib m) m))))
