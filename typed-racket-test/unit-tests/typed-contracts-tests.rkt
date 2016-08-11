#lang racket/base

;; Unit tests for typed units

(require (submod "typecheck-tests.rkt" test-helpers)
         "test-utils.rkt"
         (for-syntax racket/base
                     typed-racket/tc-setup
                     typed-racket/utils/tc-utils))

(provide tests)
(gen-test-main)

;; see typecheck-tests.rkt for rationale on imports
(require rackunit
         typed/racket/contract
         typed-racket/utils/utils
         (except-in (base-env extra-procs prims base-types base-types-extra)
                    define lambda λ case-lambda)
         (prefix-in tr: (only-in (base-env prims) define lambda λ case-lambda))
         (for-syntax (rep type-rep prop-rep object-rep)
                     (rename-in (types abbrev union numeric-tower prop-ops utils)
                                [Un t:Un]
                                [-> t:->])))

(define tests
  (test-suite
   "contract typechecking tests"
   [tc-e (>/c 10) (-FlatCon Univ -Real)]
   [tc-e any/c (-FlatCon Univ Univ)]
   [tc-e (string-len/c 3) (-FlatCon Univ -String)]
   [tc-e (->/c (string-len/c 5))
         (-Con (t:-> Univ) (t:-> -String))]
   [tc-e (->/c exact-integer? any/c)
         (-Con (t:-> -Integer Univ)
               (t:-> Univ Univ))]
   [tc-e (->/c (lambda (x) (exact-integer? x)) any/c)
         (-Con (t:-> -Integer Univ)
               (t:-> Univ Univ))]
   [tc-e (let ()
           (define (int-gt-10 x)
             (and (exact-integer? x)
                  (> 10 x)))
           (define my-any/c any/c)
           (->/c my-any/c int-gt-10))
         (-Con (t:-> Univ Univ)
               (t:-> Univ -Integer))]
   [tc-e (->/c (lambda (x) (exact-integer? x)) (</c 5) any/c)
         (-Con (t:-> -Integer -Real Univ)
               (t:-> Univ Univ Univ))]
   [tc-e (->/c (->/c exact-integer? any/c) exact-integer?)
         (-Con (t:-> (t:-> Univ Univ) Univ)
               (t:-> (t:-> -Integer Univ) -Integer))]
   [tc-e (and/c exact-integer? (</c 5))
         (-Con Univ -Integer)]
   [tc-e (and/c real? exact-integer?)
         (-Con Univ -Integer)]
   [tc-e (and/c)
         (-Con Univ Univ)]
   [tc-e (and/c (and/c exact-integer? real?) exact-integer?)
         (-Con Univ -Integer)]
   [tc-e (and/c string? exact-integer?)
         (-Con Univ (t:Un))]
   [tc-e (>/c 10) (-FlatCon Univ -Real)]
   [tc-e (</c 31) (-FlatCon Univ -Real)]
   [tc-e (=/c 13) (-FlatCon Univ -Nat)]
   [tc-e (<=/c 24) (-FlatCon Univ -Real)]
   [tc-e (>=/c 43) (-FlatCon Univ -Real)]
   [tc-e (between/c 13 31) (-FlatCon Univ -Real)]
   [tc-e (real-in 24 43) (-FlatCon Univ -Real)]
   [tc-e (integer-in 17 71) (-FlatCon Univ -PosInt)]
   [tc-e false/c (-FlatCon Univ -False)]
   [tc-e (flat-named-contract 'positive? (>/c 0))
         (-FlatCon Univ -Real)]
   [tc-e (real-in 5 10)
         (-FlatCon Univ -Real)]
   [tc-e (listof (>/c 5))
         (-Con (-lst Univ)
               (-lst -Real))]
   [tc-e (list/c (>/c 5) (string-len/c 10) (</c 10) (string-len/c 5))
         (-Con (-lst* Univ Univ Univ Univ)
               (-lst* -Real -String -Real -String))]
   [tc-e (list/c)
         (-Con Univ (-lst*))]

   [tc-e/t (let ()
             (: app-any/c (All (a) (-> (FlatCon Any Any) a Boolean)))
             (define (app-any/c any/c x)
               (any/c x))
             app-any/c)
           (-poly (a) (t:-> (-FlatCon Univ Univ) a -Boolean))]
   [tc-e (or/c exact-integer?)
         (-Con Univ -Integer)]
   [tc-e (or/c (>/c 5) (string-len/c 10))
         (-Con Univ (t:Un -Real -String))]
   [tc-e (or/c (>/c 5) exact-integer?)
         (-Con Univ (t:Un -Real -Integer))]
   ;; XXX: Disabled until or/c type rule supports higher-order
   #;[tc-e (or/c (->/c exact-integer? exact-integer?)
                 (->/c string? string? string?))
           (-Con (t:Un (t:-> -Integer Univ)
                       (t:-> -String -String Univ))
                 (t:Un (t:-> Univ -Integer)
                       (t:-> Univ Univ -String)))]
   [tc-e (or/c false/c exact-integer?)
         (-Con Univ (t:Un -False -Integer))]
   [tc-e (symbols 'foo 'bar 'baz)
         (-Con Univ -Symbol)]
   [tc-e (not/c (lambda (x) (and (exact-integer? x)
                                 (>= x 10))))
         (-FlatCon Univ Univ)]
   ;; The ->i documentation only has number? for x; I don't think that's a
   ;; good example because >=/c requires real?.
   [tc-e (->i ([x real?]
               [y (x) (>=/c x)])
              [result (x y) (>=/c (+ x y))])
         (-Con (t:-> -Real -Real Univ)
               (t:-> Univ Univ -Real))]
   ;; no dependencies, unnamed range
   [tc-e (->i ([x string?]
               [y exact-integer?]
               [z boolean?])
              [_ string?])
         (-Con (t:-> -String -Integer -Boolean Univ)
               (t:-> Univ Univ Univ -String))]
   ;; mixed mandatory keyword + plain doms
   [tc-e (->i (#:x [x real?]
               [z exact-integer?]
               #:y [y (x) (>=/c x)])
              [_ string?])
         (-Con (->key -Integer #:x -Real #t #:y -Real #t Univ)
               (->key Univ #:x Univ #t #:y Univ #t -String))]
   ;; mixed mandatory and optional dom dependencies
   [tc-e (->i ([x real?]
               [y real?])
              (#:w [w (x) (>=/c x)]
               [z (x y) (>=/c (+ x y))])
              [result (x y w z) (and/c exact-integer?
                                       (>=/c (+ x y w z)))])
         (-Con (->optkey -Real -Real (-Real) #:w -Real #f Univ)
               (->optkey Univ Univ (Univ) #:w Univ #f -Integer))]
   ;; optional keyword doms + no mandatory doms; from ->i docs
   [tc-e (->i ()
              (#:x [x real?]
               #:y [y (x) (>=/c x)])
              [result (x y) (>=/c (+ x y))])
         (-Con (->optkey () #:x -Real #f #:y -Real #f Univ)
               (->optkey () #:x Univ #f #:y Univ #f -Real))]
   [tc-e (->i ()
              [result real?])
         (-Con (t:-> Univ)
               (t:-> -Real))]
   [tc-e (->i ()
              #:rest [xs (listof real?)]
              [sum (xs) (and/c real?
                               (=/c (apply + xs)))])
         (-Con (->* (list) -Real Univ)
               (->* (list) Univ -Real))]
   [tc-e (->i ()
              #:rest [xs (lambda: ([x : (Listof Integer)]) #t)]
              [result any/c])
         (-Con (->* (list) -Integer Univ)
               (->* (list) -Integer Univ))]
   [tc-err (let ()
             (->i ()
                  #:rest [xs number?]
                  [_ any/c])
             (void))
           #:ret (ret -Void)
           #:msg "#:rest contract must be a list contract"]
   [tc-e (->i ([x real?]
               [y real?])
              (values [r1 (x) (>/c x)]
                      [r2 (r1 y) (>/c (+ r1 y))]))
         (-Con (t:-> -Real -Real (make-Values (list (-result Univ) (-result Univ))))
               (t:-> Univ Univ (make-Values (list (-result -Real) (-result -Real)))))]
   [tc-e (->i () #:pre () #t [_ any/c])
         (-Con (t:-> Univ) (t:-> Univ))]
   [tc-e (->i () [_ any/c] #:post () #t)
         (-Con (t:-> Univ) (t:-> Univ))]
   [tc-e (->i () #:pre/name () "named-pre" #t [_ any/c])
         (-Con (t:-> Univ) (t:-> Univ))]
   [tc-e (->i () [_ any/c] #:post/name () "named-post" #t)
         (-Con (t:-> Univ) (t:-> Univ))]
   [tc-err (let ()
             (->i () #:pre/desc () 0 [_ any/c])
             (void))
           #:ret (ret -Void)
           #:msg #rx"expected:(.*(Boolean|String|\\(Listof String\\)))+"]
   [tc-err (let ()
             (->i () [_ any/c] #:post/desc () 0)
             (void))
           #:ret (ret -Void)
           #:msg #rx"expected:(.*(Boolean|String|\\(Listof String\\)))+"]
   [tc-e (->i ([x natural-number/c]
               [y natural-number/c])
              [result (x y) (=/c (+ x y))]
              #:post (result x y)
              (and (= (- result x) y)
                   (= (- result y) x)))
         (-Con (t:-> -Nat -Nat Univ)
               (t:-> Univ Univ -Nat))]
   ;; Tests for various literals that Racket treats as contracts. This
   ;; should be all of the cases covered by coerce-contract/f in guts. list?
   ;; and pair?  are special-cased in guts, yet they're handled in TR by the
   ;; more general predicate coercion
   [tc-e (or/c list?)
         (-Con Univ (-lst Univ))]
   [tc-e (or/c pair?)
         (-Con Univ (-pair Univ Univ))]
   ;; The literal/predicate for the empty list seem like they should have
   ;; type (Con (Listof Any)), but that's not how it's currently
   ;; handled. Note: for contract compatibility it doesn't matter if it's
   ;; (Con Null) or (Con (Listof Any)); once these are flat contracts,
   ;; though, their current "core" type means their only type-correct
   ;; argument is '()
   [tc-e (or/c null?)
         (-Con Univ -Null)]
   [tc-e (or/c (list))
         (-Con Univ -Null)]
   ;; Typechecking symbols/keywords gives their singleton type, so that gets
   ;; carried over into the contract type. Things like chars and strings,
   ;; though, get their "top" type. This has the same issue as the (-Con
   ;; -Null) cases above.
   [tc-e (or/c 'a 'b 'c 'λ)
         (-Con Univ (t:Un (-val 'a) (-val 'b) (-val 'c) (-val 'λ)))]
   [tc-e (or/c #f #t)
         (-Con Univ -Boolean)]
   [tc-e (or/c '#:key '#:words)
         (-Con Univ (t:Un (-val '#:key) (-val '#:words)))]
   [tc-e (or/c #\a #\b #\c #\λ)
         (-Con Univ -Char)]
   [tc-e (or/c "foo" "bar")
         (-Con Univ -String)]
   (tc-e (or/c '#"baz" '#"quux")
         (-Con Univ -Bytes))
   [tc-e (or/c 5 6 7)
         (-Con Univ -PosByte)]
   [tc-e (or/c #rx"[01]+" #rx"[0123456789A-Fa-f]+")
         (-Con Univ -String)]
   [tc-e (or/c #rx#"01234" #rx#"abcd")
         (-Con Univ -Bytes)]
   [tc-e (and/c (lambda: ([x : Real]) (> x 10)))
         (-Con -Real -PosReal)]
   [tc-e (and/c exact-integer? (lambda: ([x : Integer]) (> x 0)))
         (-Con Univ -PosInt)]
   [tc-e (and/c exact-integer? string?)
         (-Con Univ (t:Un))]
   [tc-err (and/c exact-integer? (lambda: ([x : Positive-Integer]) (even? x)))]
   [tc-err (and/c exact-integer? (lambda: ([x : String]) (equal? x "foo")))]
   [tc-e (listof real?)
         (-Con (make-Listof Univ) (make-Listof -Real))]
   [tc-err (syntax/c (->/c any/c any/c))]
   [tc-e (and/c (->/c exact-integer? exact-integer?)
                (->/c zero? zero?))
         (-Con (t:-> -Integer Univ)
               (t:-> -Number -Zero))]))
