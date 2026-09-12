---
rg: 2
id: surjunctivity-is-axiomatized-by-rectangle-clauses
kind: claim
title: Surjunctive groups are exactly the models of decidably many universal rectangle clauses
distinct_from:
  strict-pairs-transfer-to-table-realizations: that transports a strict pair with a Garden-of-Eden pattern to every realization of its window tables; this replaces the pattern by the reverse rectangle, so a certificate is two local-rule identities on two rectangles, and it packages every certificate as a universal sentence whose premises and conclusions are equations.
  forward-memory-lifts-exclude-strict-cellular-sections: that excludes strictness through surjunctive covers matching the forward table; this is the exact two-table characterization in both directions and its first-order axiomatization.
  gottschalk-surjunctivity-fixed-two-generator-tester: that reduces the conjecture to one fixed host; this identifies the class of surjunctive groups syntactically, derives its permanence properties from the syntax, and shows existentially closed groups decide the conjecture.
  surjunctivity-passes-to-subgroups: that is heredity alone; this is the universal axiomatization, of which heredity is the first consequence.
artifacts:
  - research/artifacts/gottschalk-rectangle-clauses-and-recognition-2026-09-12.md
---

**ESTABLISHED** by `surjunctivity-is-axiomatized-by-rectangle-clauses-proof`.

**Data.** Finite label sets `S` and `M`, each containing a label `1`; a finite
alphabet `A`; rules `mu: A^M -> A` and `nu: A^S -> A`; an equivalence relation
`T_f` on the forward cells `S x M` and one `T_r` on the reverse cells `M x S`.
The data `D` are *strict* when

    Dec(T_f):      nu( ( mu( (p(s,m))_m ) )_s ) = p(1,1)   for every p constant on T_f-classes,
    not Enc(T_r):  mu( ( nu( (q(m,s))_s ) )_m ) != q(1,1)  for some q constant on T_r-classes.

Strictness is decidable, since it checks finitely many functions.

**Theorem.** A group `K` is not surjunctive iff, for some strict `D`, there are
elements `x_a` of `K` (`a` in `S ⊔ M`, both labels `1` sent to `1`) whose forward
products `x_s x_m` coincide along at least `T_f` and whose reverse products
`x_m x_s` coincide along at most `T_r`. Equivalently, `K` is surjunctive iff it
satisfies every universal sentence

    rho_D:  forall x  [ AND_( (s,m) T_f (s',m') )  x_s x_m = x_s' x_m' ]
                 ->   OR_( (m,s), (m',s') not T_r-related )  x_m x_s = x_m' x_s'.

The automata are `tau` with memory `(x_m)` and rule `mu`, and `sigma` with memory
`(x_s)` and rule `nu`. `sigma tau = id` is `Dec` at the realized forward table and
`tau sigma = id` is `Enc` at the realized reverse table. `Dec` is inherited by
coarser tables and `not Enc` by finer ones, which is why premises and conclusions
are both equations.

**Consequences.**
- Subgroups, ultraproducts, local embeddings, and directed colimits with arbitrary
  structure maps preserve surjunctivity; each is read off the shape of `rho_D`.
- Finite direct products are not covered: the conclusions are disjunctions, not
  Horn clauses.
- Gottschalk's conjecture holds iff some existentially closed group is surjunctive,
  iff every existentially closed group is surjunctive.
- `rho_D` holds in every group iff it holds in
  `P(D) = < x_a | x_1 = 1, x_s x_m = x_s' x_m' along T_f >`. If `D` is realized in
  any group, `P(D)` realizes it and is not surjunctive. So the conjecture says:
  for every strict `D`, some conclusion equation of `rho_D` follows from the forward
  relations in `P(D)`. This is a `Pi^0_2` sentence
  (`surjunctivity-recognition-has-a-pi2-upper-bound`).
