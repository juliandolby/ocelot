#lang rosette

(define uris '(uri1 uri2 uri3 uri4 uri5))

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(define values (append '("Rob" "Robert" "Jon" "Jonathon") (list S1 S2)))

(require ocelot)

(define U (universe (append uris values)))

(define triples (declare-relation 3 "Triples"))

(define triples-bound
  (make-exact-bound
   triples
   '((uri1 uri3 "Robert")
     (uri2 uri3 "Jonathon"))))

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

(define ex1
  (interpretation->relations
   (evaluate ib
     (solve
      (assert
       (interpret*
        (and
         (all ([s (join answers atoms)])
              (some (join s (join triples atoms))))
         (all ([s (join (join triples atoms) atoms)])
              (and
               (one (join s answers))
               (all ([v (join atoms (join s triples))])
                   (in v (join s answers))))))
        ib))))))

(define ex2
  (interpretation->relations
   (evaluate ib
     (solve
      (assert
       (interpret*
        (and
         (all ([s (join answers atoms)])
              (some (join s (join triples atoms))))
         (all ([s (join (join triples atoms) atoms)])
              (and
               (one (join s answers))
               (all ([v (join atoms (join s triples))])
                   (is-string-prefix? (join s answers) v)))))
        ib))))))

(define ex3
  (interpretation->relations
   (evaluate ib
     (solve
      (assert
       (interpret*
        (=
         answers
         (set ([s atoms] [v atoms])
              (some ([p atoms])
                    (in (-> s p v) triples))))
        ib))))))

(define ex4
  (let ((m
         (solve
          (assert
           (interpret*
            (=
             answers
             (set ([s atoms] [nn atoms])
                  (some ([p atoms] [n atoms])
                        (and (is-string-prefix? nn n)
                             (in (-> s p n) triples)))))
            ib)))))
      (interpretation->relations (evaluate ib m) m)))
