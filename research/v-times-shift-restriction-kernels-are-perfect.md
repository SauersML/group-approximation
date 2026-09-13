---
rg: 2
id: v-times-shift-restriction-kernels-are-perfect
kind: claim
title: "Restriction kernels of the alternating full group of V times the full shift are perfect at minimal subshifts"
---

With the notation of `v-times-shift-alternating-group-restrictions-are-simple`,
`G = G_V × (Z ⋉ Σ)`. For every infinite minimal subshift `Y ⊆ Σ`, the kernel
`K_Y` of the restriction `ρ_Y : A(G) -> A(G|_{C×Y})` is a perfect group.

## Attempts

- 2026-09-13 (lane z1-20-simple-fp2), **localization, proved.** Let
  `h ∈ K_Y`. At a point `(c, x) ∈ C × Y`, the element `h` is given on a
  neighbourhood in `X` by one germ `(g, σ^k)`, and it fixes `C × Y` pointwise.
  `Y` has no periodic points, so `k = 0`, and `g` fixes a neighbourhood of `c`.
  So `h` is the identity on a neighbourhood of `(c, x)` in `X`. By compactness
  it is the identity on `C × U` for some clopen `U ⊇ Y`. Hence
  `K_Y = ∪_U (A(G) ∩ [[G|_{C×(Σ∖U)}]])` over clopen `U ⊇ Y`, a directed union
  of groups supported on clopen sets that avoid `C × Y`.
- **Sufficient condition, open.** If for every clopen `W ⊆ X` disjoint from
  `C × Y` the group `A(G) ∩ [[G|_W]]` lies in a perfect subgroup of `K_Y`, for
  instance `A(G|_{W'})` for a clopen `W' ⊇ W` still avoiding `C × Y` with
  `A(G|_{W'})` perfect, then `K_Y` is perfect. Expected mechanism: the Cuntz
  factor kills homology. `H_*(G_V) = 0` because `[C] = [C_0] + [C_1] = 2[C]`,
  so by Künneth every reduction of `G` has vanishing homology. Matui-type
  abelianization formulas (`[[G]]_ab ≅ H_0(G) ⊗ Z/2 ⊕ H_1(G)` where they hold)
  would then make these full groups perfect. Their hypotheses (minimality,
  pure infiniteness) fail for non-minimal reductions and must be checked or
  replaced.
- Multisection splitting, proved: a multisection whose pieces meet `C × Y`
  splits as a product of commuting 3-cycles, one supported in any prescribed
  clopen `C × U ⊇ C × Y` and one supported away from `C × Y`. The second factor
  lies in `A(G|_W)` for a clopen `W` avoiding `C × Y`. This reduces the
  question to elements supported near `C × Y` but not on it; no swindle
  finishing the argument is known yet.
