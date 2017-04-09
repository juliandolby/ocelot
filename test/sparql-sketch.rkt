#lang rosette

(current-bitwidth #f)

(define uris '(uri1 uri2 uri3 uri4 uri5 uri6 uri7))

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(define values (append '("Rob" "Robert" "Jon" "Jonathon" "Paula" "Allison") (list S1 S2)))

(require ocelot)

(define U (universe (append uris values)))

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

(define entities (declare-relation 1 "URIs"))

(define entities-bound (make-exact-bound entities (map list uris)))

(define literals (declare-relation 1 "Literals"))

(define literals-bound (make-exact-bound literals (map list values)))

(define atoms (declare-relation 1 "Atoms"))

(define atoms-bound (make-exact-bound atoms (map list (append uris values))))

(define answers (declare-relation 2 "Map"))

(define answers-bound (make-product-bound answers uris (append uris values)))

(define limits (bounds U (list literals-bound entities-bound answers-bound atoms-bound triples-bound)))

(define ib (instantiate-bounds limits))

;;

(define (solve-it x)
  (time
   (begin
     (solver-clear (current-solver))
     (solver-assert (current-solver) (list (interpret* x ib)))
     (solver-check (current-solver)))))

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
                       (and (apply-binary-predicate
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
                         (in (-> s p v) triples))
                   (apply-unary-predicate
                    (lambda (s)
                      (and (string? s)
                           (< (string-length s) 7)))
                    v)))))))
    (interpretation->relations (evaluate ib m) m)))
