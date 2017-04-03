#lang rosette

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(require ocelot)

(define U (universe (list 'p1 'p2 "Rob" "Robert" "Jon" "Jonathon" S1 S2)))

(define String (declare-relation 1 "String"))

(define string-bound (make-exact-bound String (map list (list "Rob" "Robert" "Jon" "Jonathon" S1 S2))))

(define Person (declare-relation 1 "Person"))

(define person-bound (make-exact-bound Person '((p1) (p2))))

(define name (declare-relation 1 "name"))

(define name-bound (make-exact-bound name (map list (list "Rob" "Robert" "Jon" "Jonathon"))))

(define hasName (declare-relation 2 "hasName"))

(define has-name-bound (make-product-bound hasName '(p1 p2) (list "Rob" "Robert" "Jon" "Jonathon")))

(define hasNickname (declare-relation 2 "hasNickname"))

(define has-nickname-bound (make-product-bound hasNickname '(p1 p2) (list "Rob" "Robert" "Jon" "Jonathon")))

(define isNickname (declare-relation 2 "isNickname"))

(define is-nickname-bound (make-product-bound isNickname (list "Rob" "Robert" "Jon" "Jonathon") (list "Rob" "Robert" "Jon" "Jonathon")))

(define junk (declare-relation 1 "Junk"))

(define junk-bound (make-exact-bound junk (list (list "Jon") (list "Rob"))))

(define junk1 (declare-relation 1 "Junk1"))

(define junk1-bound (make-upper-bound junk1 (map list (list "Rob" "Robert" "Jon" "Jonathon" S1 S2))))

(define junk2 (declare-relation 1 "Junk2"))

(define junk2-bound (make-upper-bound junk2 (map list (list "Rob" "Robert" "Jon" "Jonathon" S1 S2))))

(define junk3 (declare-relation 1 "Junk3"))

(define junk3-bound (make-upper-bound junk3 (map list (list "Rob" "Robert" "Jon" "Jonathon" S1 S2))))

(define limits (bounds U (list string-bound junk1-bound junk2-bound junk3-bound junk-bound person-bound name-bound has-name-bound has-nickname-bound is-nickname-bound)))

(define ib (instantiate-bounds limits))

(define prefix-example-1
  (interpretation->relations
   (evaluate ib
     (solve
      (assert
       (interpret*
        (and
         (all [(p Person)]
              (all [(n (join p hasName))]
                   (and
                    (one (join p hasNickname))
                    (all [(s (join p hasNickname))]
                         (is-string-prefix? s n)))))
         (all [(p Person)]
              (and (one (join p hasName))
                   (all [(n (join p hasName))]
                        (and (one (join hasName n))
                             (one (join n isNickname))
                             (all [(s (join n isNickname))]
                                  (is-string-prefix? s n))))))) ib))))))

(define symbolic-example-1
  (let ((s
        (solve
         (assert
          (interpret*
           (and (some ([j junk1])
                      (some (- junk1 j)))
                (all ([s1 junk1])
                     (some ([s2 junk2])
                          (some ([s3 junk3])
                               (and
                                (is-string-prefix? s1 s2)
                                (is-string-prefix? s2 s3))))))
           ib)))))
    (println s)
    (interpretation->relations (evaluate ib s))))

(define symbolic-example-2
  (let ((s
        (solve
         (assert
          (interpret*
           (and (all ([s1 junk])
                     (some ([s2 junk2])
                           (is-string-prefix? s1 s2)))
                (all ([s2 junk2])
                      (some ([s3 junk3])
                            (is-string-prefix? s2 s3))))
           ib)))))
    (println s)
    (interpretation->relations (evaluate ib s))))