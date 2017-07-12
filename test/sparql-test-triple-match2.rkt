#lang rosette

(define _ '_)

(current-bitwidth #f)

(define all-subjects '(alice bob eve fred))
(define all-properties '(type name mbox knows))
(define all-objects '(Person "Alice" "mailto:alice@work" "Bob"  "mailto:bob@work" "mailto:bob@home" "Eve" "fred@edu"))

(define all-entities (append all-subjects all-objects (list 'Null)))
(define all-atoms (append all-entities all-properties))

(require ocelot)
(require rosette/lib/synthax)
(require rosette/lib/angelic)
(require ocelot/engine/symmetry)

(define U (universe all-atoms))

(define triples (declare-relation 3 "triples"))
(define triples-bound
  (make-exact-bound triples ;dawg-data-01             
 '(
(alice type Person)
(alice name "Alice")
(alice mbox "mailto:alice@work")
(alice knows bob)
(bob type Person)
(bob name "Bob")
(bob knows alice)
(bob mbox "mailto:bob@work")
(bob mbox "mailto:bob@home")
(eve type Person)
(eve name "Eve") 
(eve knows fred)
(fred type Person)
(fred mbox "fred@edu"))))



;assume order of bindings is according to variable occurrence in the query

(define result-dawg-tp-04 (declare-relation 1 "result-dawg-tp-04"))

(define result-dawg-tp-04-bound
  (make-exact-bound
   result-dawg-tp-04
   '(("Bob")
     ("Alice")
     ("Eve"))))

(define subjects (declare-relation 1 "subjects"))

(define subjects-bound (make-exact-bound subjects (map list all-subjects)))

(define properties (declare-relation 1 "properties"))

(define properties-bound (make-exact-bound properties (map list all-properties)))

(define objects (declare-relation 1 "objects"))

(define objects-bound (make-exact-bound objects (map list all-objects)))

(define entities (declare-relation 1 "entities"))

(define entities-bound (make-exact-bound entities (map list all-entities)))

(define atoms (declare-relation 1 "atoms"))

(define atoms-bound (make-exact-bound atoms (map list all-atoms)))

(define atom-relations (make-hash (map (lambda (a) (cons a (declare-relation 1 a))) all-atoms)))

(define atom-bounds (hash-map atom-relations (lambda (k v) (make-exact-bound v (list (list k))))))

(define (is-atom? a)
(hash-has-key? atom-relations a))

(define limits (bounds U (append atom-bounds (list subjects-bound properties-bound objects-bound entities-bound
                                              atoms-bound triples-bound
                                              result-dawg-tp-04-bound))))

(define ib (instantiate-bounds limits))

;;

(define null-rel (hash-ref atom-relations 'Null))

;;

(define (solve-it x)
 (begin
   (solver-clear (current-solver))
   (solver-assert (current-solver) (list x))
   (solver-check (current-solver))))

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

;;

(define (triple s p v)
(if (or (is-atom? s) (eq? s _))
    (let ((rel (if (eq? s _) subjects (hash-ref atom-relations s))))
      (some ([x rel])
            (triple x p v)))
    (if (or (is-atom? p) (eq? p _))
        (let ((rel (if (eq? p _) properties (hash-ref atom-relations p))))
          (some ([x rel])
                (triple s x v)))
        (if (or (is-atom? v) (eq? v _))
            (let ((rel (if (eq? v _) objects (hash-ref atom-relations v))))
              (some ([x rel])
                    (triple s p x)))
            (in (-> s p v) triples)))))

;;

(define-synthax (joins6 a1 depth)
  #:base (triple _ _ a1)
  #:else
  (choose (triple _ [choose _ a1 'alice 'bob 'eve 'fred 'type 'name 'mbox 'knows 'Person] a1)
          (some ([x subjects])
                (and
                 ;(triple x _ _ )
                 (triple x [choose 'name a1] [choose _ a1 'alice 'bob 'eve 'fred 'type 'name 'mbox 'knows 'Person
                                                     "Alice" "mailto:alice@work" "Bob"  "mailto:bob@work" "mailto:bob@home" "Eve" "fred@edu"])))))


;;

(test (dawg-triple-pattern-004 m) 
            (= result-dawg-tp-04
               (set ([o objects]) 
                    (joins6 o 2)))
    (print-forms m))

