#lang rosette

(define-symbolic S string?)

(require ocelot)

(define U (universe (append '(p1 p2 (Rob "Rob") (Robert "Robert") (Jon "Jon") (Jonathon "Jonathon")) (list (list 'S S)))))

(define String (declare-relation 1 "String"))

(define string-bound (make-exact-bound String '((Rob) (Robert) (Jon) (Jonathon) (S))))

(define Person (declare-relation 1 "Person"))

(define person-bound (make-exact-bound Person '((p1) (p2))))

(define name (declare-relation 1 "name"))

(define name-bound (make-exact-bound name '((Rob) (Robert) (Jon) (Jonathon))))

(define hasName (declare-relation 2 "hasName"))

(define has-name-bound (make-product-bound hasName '(p1 p2) '(Rob Robert Jon Jonathon)))

(define hasNickname (declare-relation 2 "hasNickname"))

(define has-nickname-bound (make-product-bound hasNickname '(p1 p2) '(Rob Robert Jon Jonathon)))

(define isNickname (declare-relation 2 "isNickname"))

(define is-nickname-bound (make-product-bound isNickname '(Rob Robert Jon Jonathon) '(Rob Robert Jon Jonathon)))

(define junk (declare-relation 1 "Junk"))

(define junk-bound (make-upper-bound junk '((p1) (Robert) (Rob))))

(define junk2 (declare-relation 1 "Junk2"))

(define junk2-bound (make-upper-bound junk2 '((Jon) (Jonathon) (Rob) (S))))

(define limits (bounds U (list string-bound junk2-bound junk-bound person-bound name-bound has-name-bound has-nickname-bound is-nickname-bound)))

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
  (interpretation->relations
   (evaluate ib
     (solve
      (assert
       (interpret*
        (some ([s1 junk2])
              (some ([s2 junk2])
                    (some ([s3 junk2])
                          (and
                           (is-string-prefix? s1 s2)
                           (is-string-prefix? s2 s3)))))
        ib))))))
