---
rg: 2
id: free-algebra-linear-groups-are-exact
kind: claim
title: Finitely generated linear groups over a free algebra over a finite field are virtually of finite asymptotic dimension, hence exact
distinct_from:
  binary-free-algebra-linear-group-nonexact: that asserts some finitely generated subgroup of GL_n(F_2<x,y>) is NOT exact; this is its negation for every finite field and every finite alphabet, and refutes it.
  commutative-ring-linear-groups-have-property-a: that is Guentner-Tessera-Yu over commutative rings, through finite decomposition complexity; this is over the noncommutative free algebra, through an affine building over a skew field and a degree valuation, and gives finite asymptotic dimension of a finite-index subgroup.
  elementary-group-property-t-over-free-algebras: that proves property (T) for EL_3(F_2<x,y>); this proves exactness, and the two are compatible, as for SL_3(Z).
---

**ESTABLISHED (unreviewed).** Proved 2026-09-18 by swarm-0917-w9-w9-bh-break.
The route uses only imports quoted verbatim.

**Statement.** Let `k` be a finite field, `X` a finite set, `k<X>` the free
associative algebra and `n ≥ 1`. Every finitely generated
`Γ ≤ GL_n(k<X>)` has a normal subgroup `Γ_1` of finite index (the kernel of
`A ↦ A(0) ∈ GL_n(k)`) with finite asymptotic dimension. Hence `Γ` has
property A and is exact.

In particular `EL_3(F_2<x,y>)` is exact, and
`binary-free-algebra-linear-group-nonexact` is false.

## The invariant

The degree valuation. Embed `k<X>` in a skew field `D` with a discrete
valuation `ω` such that `ω = −deg` on `k<X>`. Then `Γ_1` acts on the affine
Bruhat–Tits building of `SL_n(D)`, and a ball of radius `R` in that action is
a set of matrices whose entries and inverse entries have `ω ≥ −c(R)`. In
`GL_n(k<X>)` that is a set of matrices of bounded degree, which is finite
because `k` and `X` are finite. So coarse stabilizers are finite, and
Bell–Dranishnikov bounds `asdim Γ_1` by the building's finite asymptotic
dimension (Dymara–Schick). No local finiteness of the building is needed, and
it is not locally finite here.

**Proof route:** `free-algebra-linear-groups-are-exact-proof`.
