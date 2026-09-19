---
rg: 2
id: brick-groupoid-has-no-principal-cantor-factor
kind: claim
title: "The brick groupoid G_2^n has isotropy Z^{p(x)} with a countable top-rank stratum, so it is not isomorphic, even as an abstract groupoid and even after restricting both sides to nonempty open sets of units, to any product P x K in which P has uncountably many units of maximal isotropy rank; in particular not to the free Kazhdan host (M x| Gamma) x G_2"
distinct_from:
  brick-groupoid-not-isomorphic-to-kazhdan-host: that is the full non-isomorphism question for both Kazhdan hosts W1 and RS; this is the isotropy-stratum invariant, which settles the W1 half for every n and reduces the RS half to a statement about the stabilizers of the boundary action
  regular-rank-two-isotropy-blocks-spatial-realization-in-g2n: that uses the fixed-point germs of a regular rank-two isotropy group to exclude spatial realizations; this uses only the cardinality of the set of units of maximal isotropy rank, needs no topology and no regular elements, and applies to principal hosts, which have no isotropy at all
  nv-point-germ-groups-embed-in-zn-by-slope: that embeds point germ groups of nV in Z^n; this is a groupoid-isomorphism invariant counting where the top rank is attained
  nv-brick-groupoid-and-kazhdan-host-are-both-o2: that shows C*-algebras and homology do not separate; this shows the isotropy stratification does
---

**ESTABLISHED** through `brick-groupoid-has-no-principal-cantor-factor-proof`
(unreviewed, `requires: []`, self-contained).

## Setting

- `C = {0,1}^N`, `σ` the shift, and
  `G_2 = {(x, k − l, y) : σ^k x = σ^l y}` Matui's groupoid of the full one-sided 2-shift,
  as in `brick-groupoid-has-zn-cocycle-with-af-kernel`. `G_2^n` is the `n`-fold product
  groupoid (the brick groupoid of `nV`).
- `E ⊆ C` is the set of eventually periodic sequences. It is countable and dense.
- For a groupoid `𝒢` and a unit `u`, `𝒢_u^u` is the isotropy group. Where it is free
  abelian of finite rank, `rk(u)` is its rank.
- The **top stratum** `S(𝒢)` is the set of units at which `rk` attains its maximum
  (defined when all isotropy groups are free abelian of bounded finite rank).
- A groupoid isomorphism means a bijection of arrows preserving composability and
  products. No continuity is used anywhere.

## Statement

**(a) Isotropy of the brick groupoid.** For `x ∈ C^n`, the isotropy group of `G_2^n` at `x`
is `≅ Z^{p(x)}`, where `p(x)` is the number of eventually periodic coordinates of `x`. So the
maximal rank is `n`, and `S(G_2^n) = E^n` is countable and dense.

**(b) Product obstruction.** Let `𝒫`, `𝒦` be groupoids, and let `U ⊆ C^n` be a set of
units with `U ∩ E^n ≠ ∅`. Suppose `φ : 𝒫 × 𝒦 → G_2^n|_U` is an isomorphism. Then:
1. every isotropy group of `𝒫` and of `𝒦` is free abelian of rank `≤ n`, and the
   maximal ranks satisfy `R_𝒫 + R_𝒦 = n`;
2. `S(𝒫) × S(𝒦)` is countable. Hence `S(𝒫)` and `S(𝒦)`, which are nonempty, are both
   countable.

The reduction version is (c).3, which is proved directly.

**(c) Corollaries.**
1. **Principal factors.** If `𝒫` is principal (all isotropy trivial) with uncountable unit
   space, then `𝒫 × 𝒦 ≇ G_2^n` for every groupoid `𝒦` and every `n ≥ 1`.
2. **The free Kazhdan host.** For every free action `Γ ↷ M` on a Cantor set,
   `(M ⋊ Γ) × G_2 ≇ G_2^n` for every `n ≥ 1`. This holds in particular for the host `𝒢_W1` of
   `amenable-purely-infinite-groupoid-full-group-hosts-kazhdan`, whose action is free by
   Step 3 of its proof. The statement here does not depend on that route's citations: it
   holds for every free Cantor action.
3. **Kakutani / reduction version.** For nonempty open `U ⊆ C^n` and nonempty open
   `V ⊆ M × C`, `𝒢_W1|_V ≇ G_2^n|_U`. So no Kakutani-equivalence version of the isomorphism
   refutation survives either.
4. **The Robertson–Steger host, reduced.** If `(Γ ⋉ Ω) × G_2 ≅ G_2^n`, then:
   - every stabilizer `Γ_ω` is free abelian;
   - the maximal stabilizer rank is `n − 1`;
   - the set of `ω` with `rk Γ_ω = n − 1` is countable and nonempty.

   In particular, the action `Γ ↷ Ω` is not free, `n ≥ 2`, and the case `n = 1` is excluded.

## Named invariant and where the class dies

- **Invariant:** the cardinality of the top isotropy stratum.
- **Class killed:** every refutation of `brin-thompson-groups-nv-are-a-t-menable` by an
  explicit groupoid isomorphism (or Kakutani equivalence) `G_2^n ≅ 𝒫 × 𝒦` in which `𝒫` is
  principal on a Cantor set. This is the standard construction: free Cantor model ×
  purely-infinite amplifier.
- **Death step:** (b).2. The top stratum of the product contains `(top of 𝒫) × (top of 𝒦)`,
  which is uncountable, while that of `G_2^n` is `E^n`.

## What this changes

`brick-groupoid-not-isomorphic-to-kazhdan-host` recorded "No invariant recorded on the graph
separates the two groupoids". The isotropy stratification does separate them, and it is
neither a C\*-algebra nor a homology invariant nor one of the dynamical properties listed
there. So the W1 half of that necessary prerequisite holds, and the isomorphism refutation
of the flagship through W1 is dead.

What stays open is the RS half, as reduced in (c).4:
`brick-groupoid-not-isomorphic-to-rs-boundary-host`.
