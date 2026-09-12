---
rg: 2
id: kazhdan-rank-rounding-fails-over-every-field
kind: claim
title: Property (T) gives no rank-metric rounding over any field, including Q and C
distinct_from:
  kazhdan-group-rank-models-admit-no-expander-decomposition: that proves the failure for EL_3(F_2[t]) over F_2, through finite field extensions; this uses EL_3(Z[t]) and truncated polynomial quotients, so one Kazhdan group has non-rounding genuine models over every field, and its models over Q are irreducible.
  kazhdan-rank-ultraproducts-can-have-diffuse-commutants: that is the diffuse relative commutant in rank over F_2; this carries the same chain of idempotents to every field.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open F_2 rank row of the defect criterion; this removes rounding from property (T) as a proof step in every rank row, the C-linear row included, and decides no row.
artifacts:
  - research/artifacts/weakly-sofic-extension-metric-scope-2026-09-12.md
---

**ESTABLISHED.** Let `Gamma = EL_3(Z[t])` with generating set
`S = { x_ij(1), x_ij(t) : i != j }`. Fix a field `F`, `N >= 2`, and a monic `f` in `F[x]`
of degree `N`. Let

```text
rho : Gamma -> GL_3(F[x]/(f)) <= GL_(3N)(F)
```

be induced by `t -> x`. Put `S_m = span{1, x, ..., x^(m-1)}`, `m = floor(N/2)`, and
`W = S_m^3`.

1. **No rounding modulus.**
   - The invariant subspaces of `rho` are exactly the `I^3`, for ideals `I` of
     `F[x]/(f)`.
   - `dim(W + rho(s) W) - dim W <= 1` for every `s` in `S`.
   - `dim W + dim V - 2 dim(W n V) >= 3 floor(N/2)` for every invariant `V`.
   - So no `delta(eps) -> 0` places `eps n`-almost-invariant subspaces of genuine
     representations of this Kazhdan group within `delta(eps) n` of invariant ones,
     over any field.
2. **Irreducible models over `Q`.** With `f = x^N - 2` over `Q`, `rho` is irreducible, and
   `sum_s (dim(W + rho(s)W) - dim W) / dim W <= 2/m`. So irreducible `Q`-representations of
   `Gamma` are not uniform dimension expanders.
3. **Diffuse commutants.** The truncation projections `P_m` onto `S_m^3` satisfy
   `rank [P_m, rho(s)] <= 2` for every `s` in `S`. In the rank ultraproduct over `F`, they
   give idempotents `p_beta` of every rank `beta` in the relative commutant of `Gamma`,
   with `p_beta p_gamma = p_min(beta,gamma)`.

**Consequence.**
- Step (K) of the Kun--Thom normalization proof, rounding into expanding pieces, has no
  rank-metric form obtainable from property (T), in any rank row, including the
  `C`-linear row of the ladder artifact.
- Irreducible *unitary* complex representations of a Kazhdan group are dimension
  expanders (Remark 2.2 of
  `research/artifacts/kazhdan-rank-rounding-counterexample-2026-09-12.md`). So what is
  missing is the Hilbert structure, not the characteristic.

**Scope.** Models of Kazhdan groups over `F_2`-algebras, over fields of characteristic
other than two, are not reached: `F_2[t]` has no ring map into an algebra of other
characteristic. That case is open. See Section 5 of the artifact.

Derivation: `kazhdan-rank-rounding-over-every-field-proof`.
