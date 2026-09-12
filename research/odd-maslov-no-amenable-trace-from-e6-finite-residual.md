---
rg: 2
id: odd-maslov-no-amenable-trace-from-e6-finite-residual
kind: route
title: Combine C-star property T with the invisible order-three residual in the degree-six cover
target: odd-maslov-twisted-fibres-have-no-amenable-trace
requires:
  - deligne-twisted-fibres-have-no-amenable-trace
  - maslov-mod3-gap-is-metaplectic-base-degree-six-gap
  - property-t-cstar-amenable-trace-forces-fd-quotient
  - finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres
---

The mod-three fibres are already covered by
`deligne-twisted-fibres-have-no-amenable-trace`.  Consider `theta=1/6` or
`5/6`.  The fibre `A_theta` is a central summand, hence a quotient, of
`C^*(E_6)`.  Because `E_6` is a finite central extension of the Kazhdan group
`Sp_4(Z)`, `C^*(E_6)` has C-star property `(T)`, and so does `A_theta`.

If `A_theta` had an amenable trace,
`property-t-cstar-amenable-trace-forces-fd-quotient` would give a nonzero
finite-dimensional representation of `A_theta`.  Viewed as an `E_6`
representation, its central generator has character `exp(2 pi i theta)`.
In particular `z^2`, the full order-three finite residual from
`maslov-mod3-gap-is-metaplectic-base-degree-six-gap`, acts nontrivially.
This is impossible in finite dimension: a finite-dimensional unitary image
is residually finite, hence kills the full finite residual.  This is exactly
the order-six case isolated in
`finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres`.

Therefore neither order-six odd fibre has an amenable trace, completing the
four cases in `(OMAT1)`.
