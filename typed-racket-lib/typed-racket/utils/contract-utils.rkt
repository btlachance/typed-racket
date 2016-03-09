#lang racket
(require
 "utils.rkt"
 (rep type-rep filter-rep))
(provide
 (struct-out dom-info)
 (struct-out pre/post-info)
 (struct-out rng-info)
 Con*-in-ty
 Con*-out-ty
 Con*:
 confn-in
 confn-out
 confn-type-components
 ConFn*:)

;; dom-info is a (dom-info Option<Syntax> Option<Deps> Syntax ArgType Boolean)
;; Note: its components contain unexpanded/surface syntax.
;; -- `id' the syntax of the id the user wrote or false if this domain is unnamed
;; -- `deps' is either a possibly empty Listof<Syntax> for the list of
;;    identifiers this domain depends on or false if there are none (which is
;;    different from writing an empty dependency list)
;; -- `ctc' is the syntax the user wrote for the contract
;; -- `type' is either a natural number or a keyword. If it's a natural, the
;;    domain is a by-position domain, and the number indicates its relative
;;    position in the function's domain. If it's a keyword, the domain is a
;;    keyword arg and the keyword is what the user wrote for this domain. Must be
;;    unique amongst all other dom-info instances for a particular contract
;; -- `mandatory?' is #t if the domain is mandatory, #f otherwise
(struct dom-info (id deps ctc type mandatory?) #:transparent)

;; pre/post-info is a (pre/post-info Option<Syntax> Option<Deps> Syntax Natural)
;; Note: its components contain unexpanded/surface syntax.
;; -- `id' is the syntax of the id for a named pre/post condition, #f if unnamed
;; -- `deps' is either a possible empty Listof<Syntax> for the list of
;;    identifiers this condition depends on or false if there are none
;; -- `condition' is the syntax the user wrote for this condition
;; -- `position' is the relative position of this condition among other
;;    conditions of the same type
;; Note: this requires keeping the pre/post conditions separate via other means
;; and not mixing pre condition info structs with post condition info structs
(struct pre/post-info (id deps condition position) #:transparent)

;; rng-info is a (rng-info Option<Syntax> Option<Deps> Syntax Natural)
;; Note: its components contain unexpanded/surface syntax.
;; -- `id' the syntax of the id the user wrote or false if this range is unnamed
;; -- `deps' is either a possibly empty Listof<Syntax> for the list of
;;    identifiers this range depends on or false if there are none (which is
;;    different from writing an empty dependency list)
;; -- `ctc' is the syntax the user wrote for the contract, possibly even 'any' in
;;    the case of an any dependent-range
;; -- `index' is the position of the range in a possibly multi-valued range. For
;;    a non-(values ...) range, then this will simply be 0
(struct rng-info (id deps ctc index) #:transparent)

(define (Con*-in-ty ctc) (match ctc [(Con*: in out) in]))
(define (Con*-out-ty ctc) (match ctc [(Con*: in out) out]))
(define-match-expander Con*:
  (lambda (stx)
    (syntax-case stx ()
      [(_ in out)
       #'(or
          (? FlatCon? (app FlatCon-in-ty in) (app FlatCon-out-ty out))
          (? Con? (app Con-in-ty in) (app Con-out-ty out)))])))

;; A ConFnInfo is a (List Type/c Type/c) representing the in/out type components
;; of a function that could be coerced to a FlatCon

;; con-fn-in : Type/c -> Type/c
;; Assumes that ty is a Type/c that confn-type-components returns non-#f
(define (confn-in ty) (car (confn-type-components ty)))
;; confn-out : Type/c -> Type/c
;; Assumes that ty is a Type/c that confn-type-components returns non-#f
(define (confn-out ty) (cadr (confn-type-components ty)))
;; confn-type-components : Type/c -> #f or ConFnInfo
(define (confn-type-components ty)
  (match ty
    [(Function: (list (arr:
                       (list in-ty)
                       (Values: (list (Result: _ (FilterSet: (TypeFilter: out-ty _) _) _)))
                       _ _ _)))
     (list in-ty out-ty)]
    [(Function: (list (arr: (list in-ty) _ _ _ _)))
     ;; when there isn't a TypeFilter
     (list in-ty in-ty)]
    [_ #f]))
(define-match-expander ConFn*:
  (lambda (stx)
    (syntax-case stx ()
      [(_ in out)
       #'(? confn-type-components (app confn-in in) (app confn-out out))])))