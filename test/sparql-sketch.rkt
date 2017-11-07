#lang rosette

(define _ '_)

(current-bitwidth #f)

(define uris '(uri1 uri2 uri3 uri4 uri5 uri6 uri7 uri8 uri9))

(define-symbolic S1 string?)
(define-symbolic S2 string?)

(define values (append '("Rob" "Robert" "Jon" "Jonathon" "Paula" "Allison" "Christian" "Christa") (list S1 S2)))

(define all-atoms (append uris values (list 'Null #t #f)))

(require ocelot)
(require rosette/lib/synthax)
(require rosette/lib/angelic)
(require ocelot/engine/symmetry)

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

(define yes-pairs (declare-relation 2 "YesPairs"))

(define yes-pairs-bound
  (make-exact-bound
   yes-pairs
   '((uri6 "Robert")
     (uri6 "Paula")
     (uri6 "Christian"))))

(define yes-pairs2 (declare-relation 2 "YesPairs2"))

(define yes-pairs2-bound
  (make-exact-bound
   yes-pairs2
   '((uri6 "Robert")
     (uri6 "Paula")
     (uri6 "Christian")
     (Null "Jonathon")
     (Null "Allison")
     (Null "Christa"))))

(define yes-pairs3 (declare-relation 2 "YesPairs3"))

(define yes-pairs3-bound
  (make-exact-bound
   yes-pairs3
   (list (list 'uri6 S1)
         (list 'uri6 S2))))

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

(define yes-triples5 (declare-relation 3 "YesTriples5"))

(define yes-triples5-bound
(make-exact-bound
 yes-triples5
 '((uri1 uri6 "Robert")
   (uri2 Null "Jonathon")
   (uri3 uri6 "Paula")
   (uri4 Null "Allison")
   (uri8 uri6 "Christian")
   (uri9 Null "Christa"))))


(define no-triples (declare-relation 3 "NoTriples"))

(define no-triples-bound
(make-exact-bound
 no-triples
 '((uri2 uri5 "Jonathon")
   (uri3 uri5 "Allison"))))


(define entities (declare-relation 1 "URIs"))

(define entities-bound (make-exact-bound entities (map list uris)))

(define entity-or-null (declare-relation 1 "Null+URIs"))

(define entity-or-null-bound (make-exact-bound entity-or-null (cons (list 'Null) (map list uris))))

(define literals (declare-relation 1 "Literals"))

(define literals-bound (make-exact-bound literals (map list values)))

(define booleans (declare-relation 1 "Booleans"))

(define booleans-bound (make-exact-bound booleans (list (list #t) (list #f))))

(define atoms (declare-relation 1 "Atoms"))

(define atoms-bound (make-exact-bound atoms (map list all-atoms)))

(define answers (declare-relation 2 "AnswerPairs"))

(define answers-bound (make-product-bound answers (cons 'Null uris) all-atoms))

(define answer-triples (declare-relation 3 "AnswerTriples"))

(define answer-triples-bound (make-product-bound answer-triples uris (cons 'Null uris) all-atoms))

(define atom-relations (make-hash (map (lambda (a) (cons a (declare-relation 1 a))) all-atoms)))

(define atom-bounds (hash-map atom-relations (lambda (k v) (make-exact-bound v (list (list k))))))

(define (is-atom? a)
(hash-has-key? atom-relations a))

(define limits (bounds U (append atom-bounds (list booleans-bound literals-bound entities-bound entity-or-null-bound answers-bound answer-triples-bound atoms-bound triples-bound yes-pairs-bound yes-pairs2-bound yes-pairs3-bound yes-triples-bound yes-triples1-bound yes-triples2-bound yes-triples3-bound yes-triples4-bound yes-triples5-bound no-triples-bound))))

(define ib (instantiate-bounds limits))

;;

(define (solve-it x)
 (begin
   (solver-clear (current-solver))
   (solver-assert (current-solver) (list x))
   (solver-check (current-solver))))

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

(define-syntax filter
  (syntax-rules ()
    ((_ (v1 ...) x y)
     (and x (apply-predicate (lambda (v1 ...) y) v1 ...)))))

(define-syntax union
  (syntax-rules ()
    ((_ x y)
     (some ([b booleans])
           (or (filter (b) x b)
               (filter (b) y (not b)))))))

;;

(define-syntax test
  (syntax-rules ()
    ((_ (test-name model-name) formula body ...)
     (define test-name
       (time
        (let* ((f (interpret* formula ib))
               (ff (and f (generate-sbp f limits)))
               (model-name (solve-it ff)))
          (println #'test-name)
          body
          ...
          (interpretation->relations (evaluate ib model-name) model-name)))))))

(define (get-answers rel model)
  (hash-ref (interpretation->relations (evaluate ib model) model) rel))

;;

(test (ex1 model)
      (= answers
         (set ([p entities] [v literals])
              (triple 'uri1 p v)))
      (assert
       (equal?
        (get-answers answers model)
        '((uri5 "Robert")))))

(test (ex2 model)
      (= answers
         (set ([p entities] [v literals])
              (union
               (triple 'uri1 p v)
               (triple 'uri3 p v))))
      (assert
       (equal?
        (get-answers answers model)
        '((uri5 "Robert") (uri5 "Paula")))))

(test (ex3 model)
      (= answers
         (set ([p entities] [v literals])
              (filter (v)
               (union
                (triple 'uri1 p v)
                (triple 'uri3 p v))
               (< (string-length v) 6))))
      (assert
       (equal?
        (get-answers answers model)
        '((uri5 "Paula")))))

(test (ex4 model)
      (= yes-pairs2
         (set ([x entity-or-null] [v literals])
	      (some ([s entities])
	            (optional (x)
                      (triple s 'uri5 v)
                      (triple x 'uri7 s))))))
	       