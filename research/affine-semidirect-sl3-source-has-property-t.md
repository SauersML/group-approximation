---
rg: 2
id: affine-semidirect-sl3-source-has-property-t
kind: claim
title: The full integral affine group of rank three has property (T)
distinct_from:
  affine-congruence-source-is-kazhdan: that is the level-three congruence subgroup, chosen torsion-free and carrying a proper self-embedding; this is the whole integral affine group containing it with finite index, which is the group that fixes the three nested lattices in the finite-perturbation example.
  elementary-linear-semidir-pair-relative-t: that is relative property (T) for the rank-two pair over an arbitrary finitely generated ring; this is absolute property (T) for one rank-three integral group.
  elementary-group-property-t-over-free-algebras: that proves property (T) for rank-three elementary groups over free algebras on a finite field, in Lean; this is the integral affine semidirect product, and carries no Lean certification.
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

**ESTABLISHED.**  The group

```text
Gamma = Z^3 x| SL_3(Z)                                            (AT1)
```
has property (T).

Two independent derivations are recorded.

* **Finite-index permanence**, the route wired here.  `Gamma(3)` has
  finite index in `SL_3(Z)`, so `P = Gamma(3) x| Z^3` has finite index in
  `Gamma`, and property (T) passes from a finite-index subgroup to the
  ambient group.  `P` is Kazhdan by `affine-congruence-source-is-kazhdan`.
* **Direct citation**, recorded as a check.  Ershov--Jaikin-Zapirain,
  *Property (T) for noncommutative universal lattices*, Invent. Math.
  **179** (2010) 303--347: Theorem 1.1 gives property (T) for `EL_n(R)`,
  `n >= 3`, over any finitely generated unital associative ring, so
  `R = Z` gives it for `EL_3(Z) = SL_3(Z)`; Proposition 8.1, attributed
  to Kassabov, gives relative property (T) for the pair
  `(Gamma, Z^3)` at `R = Z`, `p = 3`, `q = 1`, with `EL_1(Z) = 1`.
  Combining them is the standard projection argument, written out in the
  route.

`Gamma` is **not** torsion-free, and no torsion-free claim is made for
it; the torsion-free program uses `P` instead.  What `Gamma` supplies
that `P` does not is the pointwise fixing of the three nested lattices
`Z^3`, `2^-1 Z^3`, `2^-2 Z^3` used in
`dyadic-perturbation-group-has-three-point-commuting-witness`.

DERIVATION
affine-sl3-property-t-finite-index-proof
