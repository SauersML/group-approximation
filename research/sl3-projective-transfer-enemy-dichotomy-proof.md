---
rg: 2
id: sl3-projective-transfer-enemy-dichotomy-proof
kind: route
title: Canonicalize a failed transfer, split by lattice correctability, and extract primary mass
target: sl3-projective-transfer-enemy-dichotomy
requires:
  - sl3-odd-correctable-sector-has-uniform-projective-modulus
  - fixed-projective-gap-forces-primary-congruence-mass
  - sl3-regular-projective-correction-is-inner-adjoint-stability
  - full-sl3-root-package-has-an-exact-tracial-hnn-leak
---

Enumerate the nonidentity elements `g_j` of the residually finite group
`Gamma`.  Choose a finite quotient `q_n:Gamma->Q_n` separating
`g_1,...,g_n` and replace

```text
rho_n(x) by rho_n(x) tensor lambda_(Q_n)(q_n(x)),
U_n      by U_n tensor I.
```

Normalized-HS relator defects are unchanged, every commutator is tensored
with `I`, and therefore all trace-square energies are unchanged.  The actor
character becomes canonical.

Let `a_n` be the infimum of the generator distance from
`rho_n|_Lambda` to an exact representation of `Lambda`.  On a subsequence,
either `liminf a_n>0`, which is alternative 1, or `a_n->0`; in the latter
case choose exact `sigma_n` within `a_n+1/n`.  Identity `(IAS2)` of
`sl3-regular-projective-correction-is-inner-adjoint-stability` gives the
inner-adjoint reformulation in alternative 1.

In the correctable case apply
`fixed-projective-gap-forces-primary-congruence-mass` with the fixed gap
`epsilon` from `(PED1)`.  Its estimate `(PMG4)` gives a constant `m_0>0`
such that the total dimension fraction of irreducibles with positive
`2`-conductor is at least `m_0` eventually.  This is alternative 2.  The
odd-sector modulus is the input which makes `m_0` positive.

Finally `full-sl3-root-package-has-an-exact-tracial-hnn-leak` supplies the
stated firewall: all algebraic and finite-tracial hypotheses hold in that
model while the desired conclusion fails maximally.  It is not a matrix
countermodel, so it fences proof methods without deciding either branch.

