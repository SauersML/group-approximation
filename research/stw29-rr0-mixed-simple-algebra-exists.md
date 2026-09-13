---
rg: 2
id: stw29-rr0-mixed-simple-algebra-exists
kind: claim
title: Some simple C*-algebra of real rank zero contains a nonzero finite projection and an infinite projection (negation of STW XXIX)
distinct_from:
  stw99-problem-xxix-rr0-dichotomy: that root asserts the dichotomy; this is its negation, recorded to hold the construction-side attempts and where each design dies.
---

There is a simple C\*-algebra of real rank zero containing a nonzero finite
projection and an infinite projection.  By
`stw29-counterexample-level-two-fingerprint` this is equivalent to: some
unital simple real-rank-zero `C` is finite while `M_2(C)` is infinite.

Any such algebra would simultaneously give negative answers to:
* STW XXX (it cannot be `Z`-stable, by Kirchberg's dichotomy);
* LX(1) and the Ara--Goodearl--O'Meara--Pardo separativity problem for exchange
  rings (its `V` is not separative);
* the corona factorization property for real rank zero algebras
  (`opr-cfp-rr0-dichotomy`);
* Rordam's 2005 question on stable rank one of finite simple real-rank-zero
  algebras (its finite corners have infinite stable rank).

## Attempts

* **Euler-certificate designs (Rordam).**  In
  `B = lim M(C(Z, K))`, `Z = product of S^2`, finiteness of
  `Q ~ direct_sum_(I in family) p_I` needs only Hall's condition on the index
  family (Acta 2003, Proposition 4.5(i)).  Rordam's 2005 proof that real rank
  zero fails uses more: a coordinate `s_n` lying in no index set at stage `n`,
  propagated by `s_(n+1) = nu(0, s_n)`.  Injectivity of `nu` forces such free
  coordinates (RRnot0, Lemma 3.1).  Villadsen's transversality (RRnot0,
  Proposition 2.2) only protects cohomology of factors other than the one
  carrying the sign change.  So a design in which every coordinate is
  eventually absorbed into the index families evades that specific
  obstruction.  Where it dies: nothing is known that proves real rank zero for
  such a limit.  Every self-adjoint element, not only coordinate functions,
  would have to cut spectrally while Hall families keep certifying finiteness,
  and no mechanism is known that kills Euler classes on all generic zero sets
  while keeping them globally.
* **Index-certificate designs (Clarke--Blackadar).**  The non-simple example
  `0 -> K -> E -> C(S^3) -> 0` with nonzero index map has `E` finite and
  `M_2(E)` infinite (Acta 2003, Remark 7.10).  Its certificate is odd (`K_1` of
  the quotient) and so is not protected by transversality.  Firewall: if
  unital blocks `E_n` are extensions of residually finite-dimensional
  quotients `Q_n` by `I_n = K` (or any ideal with no nonzero finite-dimensional
  representation), and the connecting maps are unital and injective, then the
  limit is never simple.  Every finite-dimensional irreducible representation
  of `Q_(n+1)` kills `phi_n(I_n)`, so `phi_n(I_n) subset I_(n+1)`.  The closure
  of the union of the images of the `I_n` is then a nonzero ideal, and it is
  proper because `||1 - j|| >= 1` for `j in I_m` at every stage.  An index
  design needs non-RFD quotients, i.e. towers of extensions, which are not
  analysed.
* **Zero-dimensional crossed products.**  `D rtimes Gamma` with simple
  coefficients carrying a state-ordered dense `K_0` is always dichotomous
  (`simple-coefficient-crossed-products-dichotomy`,
  `simple-af-integer-crossed-products-dichotomy`).  Non-simple AF coefficients
  with minimal actions remain open.  Lexicographic `Z`-chains of ideals give
  pure infiniteness, so only twisted orders could help.
* **Limits of separative blocks.**  These are never mixed
  (`stw29-separative-projection-monoid-dichotomy`).  A counterexample needs
  non-separative building blocks cofinally.
* **Abstract monoids.**  Countable mixed simple refinement monoids exist:
  apply `opr-mixed-simple-refinement-monoid` and take a countable elementary
  submonoid containing `u` and a witness for `4u <= 2u`, which preserves
  refinement, simplicity, finiteness of `u` and proper infiniteness of `2u`.
  So the question is exactly C\*-realizability of such a monoid by a
  real-rank-zero simple algebra.
