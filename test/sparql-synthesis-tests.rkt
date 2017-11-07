(require "sparql-synthesis-sketch.rkt")

;;

(test (ex1 model)
      (and
       (all ([s (join answers literals)])
            (some (join s (join triples literals))))
       (all ([s (join (join triples literals) entities)])
            (and
             (one (join s answers))
             (all ([v (join atoms (join s triples))])
                  (in v (join s answers)))))))

(test (ex2 model)
      (and
       (all ([s (join answers literals)])
            (some (join s (join triples literals))))
       (all ([s (join (join triples literals) entities)])
            (and
             (one (join s answers))
             (all ([v (join entities (join s triples))])
                  (is-string-prefix? (join s answers) v))))))

(test (ex3 model)
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
                        (in (-> s p n) triples)))))))

(test (ex4 m)
      (=
       answers
       (set ([s entities] [nn literals])
            (some ([p entities] [n literals])
                  (and (is-string-prefix? nn n)
                       (in (-> s p n) triples))))))

(test (ex5 m)
      (= answers
         (set ([s entities] [v literals])
              (some ([t entities])
                    (and
                     (some ([p1 entities])
                           (in (-> s p1 t) triples))
                     (some ([p2 entities])
                           (in (-> t p2 v) triples)))))))

(test (ex6 m)
      (= answers
         (set ([s entities] [v literals])
              (and
               (some ([p entities])
                     (triple s p v))
               (apply-predicate
                (lambda (s)
                  (and (string? s)
                       (< (string-length s) 7)))
                v)))))

(test (ex7 m)
      (= answers
         (set ([s entities] [v literals])
              (triple s 'uri5 v))))

(test (ex8 m)       
      (= answers
         (set ([s entities] [v literals])
              (and
               (triple _ _ s)
               (triple s 'uri5 v)))))

(test (ex9 m)
      (= answers
         (set ([s entities] [v literals])
              (and
               (apply-predicate
                (lambda (s)
                  (and (string? s) (> (string-length s) 6)))
                v)
               (triple s 'uri5 v)))))


(test (ex10 m) 
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
      (assert (<= i1 (apply max (map (lambda (t) (string-length (car t)))
                                     (hash-ref (interpretation->relations (evaluate ib m) m) literals)))))
      (print-forms m)
      (println (evaluate i1 m)))

(test (ex11 m) 
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

      (map (lambda (i) (assert (<= i (+ (litlen-max m) 1))))  (list i2 i3 i4 i5 i6))

      (print-forms m)
      (println (evaluate i3 m))
      (println (evaluate i4 m)))


(test (ex12 m)
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
                              (triple s1 'uri5 v1)))))))))

(test (ex13 m)
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
                       v v1))))))))

(test (ex14 m)
      (= answers
         (set ([s entities] [v literals])
              (ppx (_ _) s v))))

(test (ex15 m) 
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

      (map (lambda (i) (assert (<= i (litlen-max m) )))  (list i2 i3 i4 i5 i6))

      (print-forms m)
      (println (evaluate i3 m))
      (println (evaluate i4 m)))

(define null-rel (hash-ref atom-relations 'Null))

(test (ex16 m)
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
                                     (triple s2 'uri7 s1)))))))))))

(test (ex17 m)
      (= answer-triples
         (set ([s entities] [x atoms] [v literals])
              (and
               (triple s 'uri5 v)
               (or
                (triple x 'uri7 s)
                (and
                 (in x null-rel)
                 (not (triple _ 'uri7 s))))))))

(test (ex18 m) 
      (= answer-triples
         (set ([s entities] [x atoms] [v literals])
              (optional (x) (triple s 'uri5 v) (triple x 'uri7 s)))))

; arguments: orexpr1 ...
; with orexp1 := (andexpr1 ...)
;(define-syntax filter
;  (syntax-rules () 
;    ((_ (nexpr ...) ...)
;     (or (and nexpr ...) ...))))


(test (ex19 m)
      (= yes-triples3
         (set ([s entities] [x atoms] [v literals]) 
              (filter (v) (triple s x v) (boundedfilter v))))
    ;(assert-max sintegers (litlen-max m))
      (print-forms m)
      (printeval m sintegers))

(test (ex20 m)
      (= yes-triples3
         (set ([s entities] [x atoms] [v literals]) 
              (and (triple s x v)
                   (apply-predicate
                    (lambda (x) (and (string? x) (bound (string-length x))))
                    v))))
      (print-forms m))

(test (ex21 m)
      (= answer-triples
         (set ([s entities] [x uri5-rel] [v literals])
              (and (triple s x v) 
                   (not (in (-> s x v) yes-triples3))))))

(test (ex22 m)
      (= (set ([s entities] [x uri5-rel] [v literals])
              (and (triple s x v) 
                   (not (in (-> s x v) yes-triples3))))
         (set ([s entities] [x atoms] [v literals]) 
              (and (triple s x v)
                   (apply-predicate
                    (lambda (x) (and (string? x) (bound (string-length x))))
                    v))))
      (print-forms m))

(test (ex23 m)
      (= (set ([s entities] [v literals])
              (triple s 'uri5 v))
         (set ([s entities] [v literals])
              [choose (triple s 'uri5 v) (triple s 'uri7 v)]))
      (print-forms m))

(test (ex24 m)
      (= yes-triples4
         (set ([s entities] [x atoms] [v1 literals]) 
              (some ([v2 literals])
                    (and (triple s x v2)
                         (apply-predicate
                          (lambda (x y)
                            (and (not (equal? x y)) (string-prefix? y x)))
                          v2 v1))
                    )))
      (print-forms m)
      (printeval m (list S1 S2)))

(test (ex25 m)
      (= yes-triples4
         (set ([s entities] [x atoms] [v1 literals]) 
              (some ([v2 literals]) (and (triple s x v2) (apply-predicate (lambda (x y) (boundedstrfilter x y)) v2 v1))
                    )))
      (print-forms m)
      (printeval m (list S1 S2)))


(test (ex26 m) 
            (= yes-triples3
               (set ([s entities] [x atoms] [v1 literals]) 
                    (joins s x v1 2)))
    (print-forms m))

(test (ex27 m)
             (= (set ([s entities] [x uri5-rel] [v literals])
                     (and (triple s x v) 
                          (not (in (-> s x v) yes-triples3))))
                (set ([s entities] [x atoms] [v1 literals]) 
                     (joins s x v1 2)))
    (print-forms m))

(test (ex28 m)
      (= yes-pairs
         (set ([s entities] [v literals])
              (joins2 s v 2)))
      (print-forms m))

(test (ex29 m)
      (= yes-pairs2
         (set ([s atoms] [v literals])
              (joins3 s v 2)))
      (print-forms m))

(test (ex30 m)
      (all ([n (join entities yes-pairs3)])
           (some ([nn literals])
                 (apply-predicate is-true-prefix nn n)))
      (printeval m (list S1 S2)))
           
(test (ex31 m)
      (all ([n (join entities yes-pairs3)])
           (some ([nn literals])
                 (apply-predicate (lambda (x y) (and (is-true-prefix x y) (string-suffix? y " A."))) nn n)))
      (printeval m (list S1 S2)))

;(test (ex32 m)
;      (= yes-pairs2
;         (set ([s atoms] [v literals])
;              (joins4 s v 2)))
;      (print-forms m))

