#lang racket
(provide
 (struct-out dom-info)

;; dom-info is a (dom-info Option<Syntax> Option<Deps> Syntax ArgType Boolean)
;; -- `id' the syntax of the id the user wrote or false if this domain is unnamed
;; -- `deps' is either a possibly empty Listof<Syntax> for the list of
;;    identifiers this domain depends on or false if there are none (which is
;;    different from writing an empty dependency list)
;; -- `ctc' is the syntax the user wrote for the contract
;; -- `type' is either a natural number or a keyword. If it's a natural, the
;;    domain is a by-position domain, and the number indicates its relative
;;    position in the function's domain. If it's a keyword, the domain is a
;;    keyword arg and the keyword is what the wrote for this domain
;; -- `mandatory?' is #t if the domain is mandatory, #f otherwise
(struct dom-info (id deps ctc type mandatory?) #:transparent)

;; pre/post-info is a (pre/post-info Option<Syntax> Option<Deps> Syntax Natural)
;; -- `id' is the syntax of the id for a named pre/post condition, #f if unnamed
;; -- `deps' is either a possible empty Listof<Syntax> for the list of
;;    identifiers this condition depends on or false if there are none
;; -- `condition' is the syntax the user wrote for this condition
;; -- `position' is the relative position of this condition among other
;;    conditions of the same type
;; Note: this requires keeping the pre/post conditions separate via other means
;; and not mixing pre condition info structs with post condition info structs
(struct pre/post-info (id deps condition position))

;; dependent-rng is a (dependent-rng RngInfo) where RngInfo is one of
;; -- #f
;; -- id+ctc
;; -- (listof id+ctc)
;; TODO: rework this so that we have a separate id+ctc struct?
(struct dependent-rng (info))
