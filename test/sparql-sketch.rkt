#lang rosette

(define _ '_)

(current-bitwidth #f)

(define uris '(uri1 uri2 uri3 uri4 uri5 uri6 uri7 uri8 uri9))

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(define values (append '("Rob" "Robert" "Jon" "Jonathon" "Paula" "Allison" "Christian" "Christa") (list S1 S2)))

(define all-atoms (append uris values (list 'Null)))

(require ocelot)
(require rosette/lib/synthax)
(require rosette/lib/angelic)

(define U (universe all-atoms))

(define triples (declare-relation 3 "Triples"))

(define triples-bound
  (make-exact-bound
   triples
   '((uri1 uri5 "Robert")
     (uri2 uri5 "Jonathon")
     (uri3 uri5 "Paula")
     (uri4 uri5 "Allison")
     (uri8 uri5 "Christian")
     (uri9 uri5 "Christa")
     (uri6 uri7 uri1)
     (uri6 uri7 uri3)
     (uri6 uri7 uri8))))

(define yes-triples (declare-relation 3 "YesTriples"))

(define yes-triples-bound
  (make-exact-bound
   yes-triples
   '((uri1 uri5 "Robert")
     (uri3 uri5 "Paula"))))

(define yes-triples1 (declare-relation 3 "YesTriples1"))

(define yes-triples1-bound
  (make-exact-bound
   yes-triples1
   '((uri1 uri5 "Robert")
     (uri3 uri5 "Paula")
     (uri8 uri5 "Christian"))))

(define yes-triples2 (declare-relation 3 "YesTriples2"))

(define yes-triples2-bound
  (make-exact-bound
   yes-triples2
   '((uri1 uri5 "Robert")
     (uri3 uri5 "Paula")
     (uri8 uri5 "Christian")
     (uri8 uri5 "Christa"))))

(define yes-triples3 (declare-relation 3 "YesTriples3"))

(define yes-triples3-bound
  (make-exact-bound
   yes-triples3
   '((uri2 uri5 "Jonathon")
     (uri4 uri5 "Allison")
     (uri9 uri5 "Christa"))))

(define yes-triples4 (declare-relation 3 "YesTriples4"))

(define yes-triples4-bound
  (make-exact-bound
   yes-triples4
   (list
    (list 'uri3 'uri5 S1)
    (list 'uri4 'uri5 S2))))

(define no-triples (declare-relation 3 "NoTriples"))

(define no-triples-bound
  (make-exact-bound
   no-triples
   '((uri2 uri5 "Jonathon")
     (uri3 uri5 "Allison"))))


(define entities (declare-relation 1 "URIs"))

(define entities-bound (make-exact-bound entities (map list uris)))

(define literals (declare-relation 1 "Literals"))

(define literals-bound (make-exact-bound literals (map list values)))

(define atoms (declare-relation 1 "Atoms"))

(define atoms-bound (make-exact-bound atoms (map list all-atoms)))

(define answers (declare-relation 2 "AnswerPairs"))

(define answers-bound (make-product-bound answers uris all-atoms))

(define answer-triples (declare-relation 3 "AnswerTriples"))

(define answer-triples-bound (make-product-bound answer-triples uris (cons 'Null uris) all-atoms))

(define atom-relations (make-hash (map (lambda (a) (cons a (declare-relation 1 a))) all-atoms)))

(define atom-bounds (hash-map atom-relations (lambda (k v) (make-exact-bound v (list (list k))))))

(define (is-atom? a)
  (hash-has-key? atom-relations a))

(define limits (bounds U (append atom-bounds (list literals-bound entities-bound answers-bound answer-triples-bound atoms-bound triples-bound yes-triples-bound yes-triples1-bound yes-triples2-bound yes-triples3-bound yes-triples4-bound no-triples-bound))))

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

(define-symbolic* i1 i2 i3 i4 i5 i6 i7 integer?)

(define sintegers (list i1 i2 i3 i4 i5 i6 i7))

; comparison operators
(define (comp-eq i) (= i i2))
(define (comp-le i) (<= i i3))
(define (comp-l i) (< i i4))
(define (comp-ge i) (>= i i5))
(define (comp-g i) (> i i6))
(define (comp-uneq i) (not (= i i7)))

;create simple numeric expression
(define (numeric pred v)
  (and (string? v) (pred (string-length v))))

(define (strlen s)
  (apply-predicate (lambda (v) (if (string? v) (string-length v) -1)) s))

(define (assert-max svalues max) (map (lambda (i) (assert (<= i (+ max 1)))) svalues))

(define (litlen-max model) (apply max (map (lambda (t) (string-length (car t)))
                                    (hash-ref (interpretation->relations (evaluate ib model) model) literals))))

(define (printeval model svalues) (println (map (lambda (i) (evaluate i model)) svalues)))


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
           (some answers)
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
     (interpretation->relations (evaluate ib m) m)))


(define (strlen-comp s) (and (string? s) ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s))))

(define (strlen-comp-union s) (and (string? s)
                                   (or ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s))
                                   ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s)))))

(define ex11
  (let ((m (solve-it
           (and
             (= answers (set ([s entities] [v literals])
                              (and (apply-predicate (lambda (vv) ([choose strlen-comp strlen-comp-union] vv)) v)
                                   (some ([p entities]) (triple s p v)))
               ))
             
             (all ([s (join (join yes-triples literals) entities)])
              (and (some (join s answers))
                   (all ([v (join atoms (join s yes-triples))]) (in v (join s answers)))))
             
             (all ([s (join (join no-triples literals) entities)])
              (all ([v (join atoms (join s no-triples))]) (not (in v (join s answers)))))
            )
         )))

    (map (lambda (i) (assert (<= i (+ (litlen-max m) 1))))  (list i2 i3 i4 i5 i6))

    (print-forms m)
    (println (evaluate i3 m))
    (println (evaluate i4 m))
    (interpretation->relations (evaluate ib m) m)))


(define ex12
  (let ((m
         (solve-it
          (= answers
             (set ([s entities] [v literals])
                  (and
                   (apply-predicate
                    (lambda (s)
                      (and (string? s) (> (string-length s) 6)))
                    v)
                   (triple s 'uri5 v)
                   (not (in (-> s v)
                            (set ([s1 entities] [v1 literals])
                                 (and
                                  (apply-predicate
                                   (lambda (s)
                                     (and (string? s) (> (string-length s) 7)))
                                   v1)
                                  (triple s1 'uri5 v1)))))))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex13
  (let ((m
         (solve-it
          (and
           (some ([v2 (join entities answers)])
                 (apply-predicate
                  (lambda (v) (equal? v "AllisonOne"))
                  v2))
           (some ([v2 (join entities answers)])
                 (apply-predicate
                  (lambda (v) (equal? v "PaulaOne"))
                  v2))
           (= answers
              (set ([s entities] [v literals])
                   (some
                    (set ([v1 literals])
                         (and
                          (triple s 'uri5 v1)
                          (apply-predicate
                           (lambda (a b)
                             (and (string-prefix? a b)
                                  (not (equal? a b))))
                           v v1))))))))))
    (interpretation->relations (evaluate ib m) m)))

(define-syntax ppx
  (syntax-rules ()
    ((_ (pred) from to)
     (triple from pred to))
    ((_ (pred1 pred2 ...) from to)
     (let ((s (gensym)))
       (some ([s entities])
	     (and
	      (triple from pred1 s)
	      (ppx (pred2 ...) s to)))))))


(define ex14
  (let ((m
	 (solve-it
	  (= answers
	     (set ([s entities] [v literals])
		  (ppx (_ _) s v))))))
    (interpretation->relations (evaluate ib m) m)))



(define ex15
  (let ((m (solve-it
           (and
             (= answers (set ([s entities] [v literals])
                              (and (apply-predicate (lambda (vv) ([choose strlen-comp strlen-comp-union] vv)) v)
                                   (some ([p entities]) (triple s p v)))
               ))
             
             (all ([s (join (join yes-triples1 literals) entities)])
              (and (some (join s answers))
                   (all ([v (join atoms (join s yes-triples1))]) (in v (join s answers)))))
             
             (all ([s (join (join no-triples literals) entities)])
              (all ([v (join atoms (join s no-triples))]) (not (in v (join s answers)))))
            )
         )))

    (map (lambda (i) (assert (<= i (litlen-max m) )))  (list i2 i3 i4 i5 i6))

    (print-forms m)
    (println (evaluate i3 m))
    (println (evaluate i4 m))
    (interpretation->relations (evaluate ib m) m)))

(define ex16
  (let* ((null-rel (hash-ref atom-relations 'Null))
         (m
         (solve-it
          (= answer-triples
             (set ([s entities] [x atoms] [v literals])
                  (and
                   (triple s 'uri5 v)
                   (or
                    (triple x 'uri7 s)
                    (and
                     (in x null-rel)
                     (not (in s
                              (set ([s1 entities])
                                   (some ([s2 entities])
                                         (triple s2 'uri7 s1)))))))))))))
    (interpretation->relations (evaluate ib m) m)))

(define ex17
  (let* ((null-rel (hash-ref atom-relations 'Null))
         (m
         (solve-it
          (= answer-triples
             (set ([s entities] [x atoms] [v literals])
                  (and
                   (triple s 'uri5 v)
                   (or
                    (triple x 'uri7 s)
                    (and
                     (in x null-rel)
                     (not (triple _ 'uri7 s))))))))))
    (interpretation->relations (evaluate ib m) m)))

(define-syntax optional
  (syntax-rules ()
    ((_ (v1 ...) x y)
     (let* ((null-rel (hash-ref atom-relations 'Null)))
        (and x
            (or y
                (and 
                 (and (in v1 null-rel) ...)
                 (no [(v1 atoms) ...]
                     y))))))))

(define ex18
  (let ((m (solve-it
            (= answer-triples
               (set ([s entities] [x atoms] [v literals])
                    (optional (x) (triple s 'uri5 v) (triple x 'uri7 s)))))))
    (interpretation->relations (evaluate ib m) m)))

; arguments: orexpr1 ...
; with orexp1 := (andexpr1 ...)
;(define-syntax filter
;  (syntax-rules () 
;    ((_ (nexpr ...) ...)
;     (or (and nexpr ...) ...))))


;and/or are considered to be binary currently
(define-synthax (filter-it i depth)
#:base (numeric [choose comp-eq comp-le comp-l comp-ge comp-g comp-uneq] i)
#:else (choose
        (numeric [choose comp-eq comp-le comp-l comp-ge comp-g comp-uneq] i)
        (and (filter-it i (- depth 1)) (filter-it i (- depth 1)))
        (or (filter-it i (- depth 1)) (filter-it i (- depth 1)))))
     
; The body of filter-bounded is a hole to be filled with an
; expression of depth (up to) 1 from the filter grammar.
(define (boundedfilter i)
  (filter-it i 1))

(define ex19
  (let ((m (solve-it
            (= yes-triples3
               (set ([s entities] [x atoms] [v literals]) 
                    (and (triple s x v) (apply-predicate (lambda (x) (boundedfilter x)) v)))))))
    ;(assert-max sintegers (litlen-max m))
    (print-forms m)
    (printeval m sintegers)
    (interpretation->relations (evaluate ib m) m)
    ))

(define (andf x y) (and x y))

(define (orf x y) (or x y))

(define (bound x)
  ([choose andf orf]
   ([choose < = >] x (?? integer?))
   ([choose < = >] x (?? integer?))))
          
(define ex20
  (let ((m (solve-it
            (= yes-triples3
               (set ([s entities] [x atoms] [v literals]) 
                    (and (triple s x v)
                         (apply-predicate
                          (lambda (x) (and (string? x) (bound (string-length x))))
                          v)))))))
    (print-forms m)
    (interpretation->relations (evaluate ib m) m)
    ))

(define ex21
    (let* ((uri5-rel (hash-ref atom-relations 'uri5))
           (m (solve-it
               (= answer-triples
                  (set ([s entities] [x uri5-rel] [v literals])
                       (and (triple s x v) 
                            (not (in (-> s x v) yes-triples3))))))))
      (interpretation->relations (evaluate ib m) m)))

(define ex22
  (let* ((uri5-rel (hash-ref atom-relations 'uri5))
         (m (solve-it
             (= (set ([s entities] [x uri5-rel] [v literals])
                     (and (triple s x v) 
                          (not (in (-> s x v) yes-triples3))))
                (set ([s entities] [x atoms] [v literals]) 
                     (and (triple s x v)
                          (apply-predicate
                           (lambda (x) (and (string? x) (bound (string-length x))))
                           v)))))))
    (print-forms m)
    (interpretation->relations (evaluate ib m) m)
    ))

(define ex23
  (let ((m
         (solve-it
          (= (set ([s entities] [v literals])
                  (triple s 'uri5 v))
             (set ([s entities] [v literals])
                  [choose (triple s 'uri5 v) (triple s 'uri7 v)])))))
    (print-forms m)
    (interpretation->relations (evaluate ib m) m)))

(define (is-true-prefix x y) (and (not (equal? x y)) (string-prefix? y x)))

;and/or are considered to be binary currently
(define-synthax (strfilter-it s1 s2 depth)
#:base ([choose is-true-prefix equal?] s1 s2)
#:else (choose
        ([choose is-true-prefix equal?] s1 s2)
        (and (strfilter-it s1 s2 (- depth 1)) (strfilter-it s1 s2 (- depth 1)))
        (or (strfilter-it s1 s2 (- depth 1)) (strfilter-it s1 s2 (- depth 1)))))


(define (boundedstrfilter s1 s2)
  (strfilter-it s1 s2 1))

(define ex24
  (let ((m (solve-it
            (= yes-triples4
               (set ([s entities] [x atoms] [v1 literals]) 
                    (some ([v2 literals])
                          (and (triple s x v2)
                               (apply-predicate
                                (lambda (x y)
                                  (and (not (equal? x y)) (string-prefix? y x)))
                                v2 v1))
                     ))))))
    (print-forms m)
    (printeval m (list S1 S2))
    (interpretation->relations (evaluate ib m) m)))

(define ex25
  (let ((m (solve-it
            (= yes-triples4
               (set ([s entities] [x atoms] [v1 literals]) 
                    (some ([v2 literals]) (and (triple s x v2) (apply-predicate (lambda (x y) (boundedstrfilter x y)) v2 v1))
                     ))))))
    (print-forms m)
    (printeval m (list S1 S2))
    (interpretation->relations (evaluate ib m) m)))

(define-synthax (joins s p v depth)
  #:base (triple [choose s p v] [choose s p v] [choose s p v])
  #:else (choose
          (joins s p v (- depth 1))
          (and (joins s p v (- depth 1)) (joins s p v (- depth 1)))
          (and (joins s p v (- depth 1))
               (apply-predicate (lambda (x) (and (string? x) (bound (string-length x)))) [choose s p v]))))

(define ex26
  (let ((m (solve-it
            (= yes-triples3
               (set ([s entities] [x atoms] [v1 literals]) 
                    (joins s x v1 2))))))
    (print-forms m)
    (interpretation->relations (evaluate ib m) m)))


(define ex27
  (let* ((uri5-rel (hash-ref atom-relations 'uri5))
         (m (solve-it
             (= (set ([s entities] [x uri5-rel] [v literals])
                     (and (triple s x v) 
                          (not (in (-> s x v) yes-triples3))))
                (set ([s entities] [x atoms] [v1 literals]) 
                     (joins s x v1 2))))))
    (print-forms m)
    (interpretation->relations (evaluate ib m) m)))


