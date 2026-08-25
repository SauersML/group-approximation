---
rg: 2
id: atlas-stable-torsion-cancellation-proof
kind: route
title: Block-amplify and conjugate-realify the regular two-A8 relative unitary
target: atlas-regular-face-kills-stable-torsion-invariants
requires:
  - atlas-phase-cycle-determinant-is-gauge-trivial
  - additive-index-instability
  - fixed-rank-index-authenticator-has-gap-or-functoriality
---

Choose the standard basis of `l^2(A8)`, so every `rho_k(g)` is real.  For a
word `w in A8*A8`, evaluation at `U directSum V` is the block sum of its
evaluations at `U` and `V`.  The same is true of every integral linear row
`rho(z_j)U`.  Normalized Hilbert--Schmidt square on blocks is the
dimension-weighted average, proving `(ATK1)`.  Entrywise conjugation commutes
with word evaluation and with every real integral row, proving `(ATK2)` and
then `(ATK3)`.

Write `U=X+iY`.  The standard fixed change of basis from
`U directSum conjugate(U)` gives

```text
R(U)=[[X,-Y],[Y,X]],
```

which is real orthogonal because `U` is unitary.  That change of basis is a
two-by-two scalar block matrix, so it commutes with
`rho_k(g) directSum rho_k(g)` for every `g`.  Simultaneous conjugation by it
therefore preserves every word defect and every row norm.  This proves
`(ATK4)`.

The determinant of the regular representation is a homomorphism
`A8 -> {+1,-1}`.  Since `A8` is perfect, the homomorphism is trivial.  Both
marked chart images therefore lie in `SU(dk)`, including the second chart
after conjugation by an arbitrary `U`.  Multiplicativity proves `(ATK5)` for
every free-product word.  The standard eigenvalue count for exterior powers,
in which each eigenvalue occurs in exactly `binomial(dk-1,r-1)` wedge
monomials, proves `(ATK6)`.

Stable K-theory classes and determinant-line parities add under block sum.
If their target has exponent `e`, `(ATK3)` provides the amplified point and
additivity gives `(ATK7)`.  For an orientation-odd class, additivity and
`kappa(conjugate(U))=-kappa(U)` instead give cancellation in the realification
`(ATK4)`.  In both cases the six-word defect and positive five-row payload
are unchanged.  This proves the claimed fence.
