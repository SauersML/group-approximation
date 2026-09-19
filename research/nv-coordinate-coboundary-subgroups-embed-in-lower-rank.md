---
rg: 2
id: nv-coordinate-coboundary-subgroups-embed-in-lower-rank
kind: claim
title: "A finitely generated subgroup of nV one of whose coordinate level cocycles is a continuous coboundary embeds in (n-1)V (and is finite for n = 1); so Kazhdan finiteness in nV reduces to Kazhdan finiteness in (n-1)V plus straightening one coordinate"
distinct_from:
  nv-subgroups-with-sign-definite-rank-one-slopes-embed-in-v: that recodes slope blocks and freezes coordinates whose slope is identically zero; this allows the frozen coordinate to have any slope that is a continuous coboundary, which is not known to be removable by conjugation inside nV (a conjugator would need h as its own coordinate level, and a coordinate-1-only conjugator would need a Kraft equality that need not hold), and it puts no condition at all on the other coordinates.
  brin-thompson-torsion-has-clopen-fixed-sets: item 4 there says H is finite iff the whole Z^n cocycle is a continuous coboundary; this needs only one coordinate and concludes an embedding one rank down, so it iterates into an induction on n.
  finitely-generated-subgroups-of-nv-are-finite-iff-germ-finite: that is a finiteness criterion by bounded offsets at points; this is an embedding criterion by one continuous transfer function.
  cantor-maps-by-v-embed-in-next-brin-thompson-group: that embeds groups one rank up; this embeds a class of subgroups one rank down.
  af-by-zk-full-groups-have-finite-kazhdan-subgroups: that asked for finiteness of Kazhdan subgroups from an AF-kernel Z^k cocycle for general groupoids and is refuted; this uses the AF skew product of one coordinate of G_2^n only, keeping the product structure the refuting host lacks.
---

**ESTABLISHED** by `nv-coordinate-coboundary-subgroups-embed-in-lower-rank-proof`
(lane swarm-0917-w16-w16-z-last1, 2026-09-19, elementary, not independently reviewed; the
AF structure of the gauge skew product of the Cuntz groupoid is standard, and no priority is
claimed for it). Item 1 imports nothing. Items 2 and 3 use the textbook fact that Kazhdan
groups are finitely generated (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*,
Theorem 1.3.1), item 4 of `brin-thompson-torsion-has-clopen-fixed-sets`, and, for the `2V`
case of item 3, `thompson-v-has-haagerup-property`.

## Setting

`C = {0,1}^N`, and `nV` is Brin's group of homeomorphisms of `C^n` given by finitely many brick
prefix replacements `(p_1 w_1, ..., p_n w_n) -> (q_1 w_1, ..., q_n w_n)`. The level cocycle is
`c_g(y) = (|q_j| - |p_j|)_j ∈ Z^n` on a brick containing `y`; it is well defined, locally
constant and satisfies `c_(gk)(y) = c_g(k y) + c_k(y)` (item 1 of
`brin-thompson-torsion-has-clopen-fixed-sets`). Write `c_{g,i}` for its `i`-th coordinate.
Set `0V := 1` (the trivial group).

## Statement

1. **Coordinate straightening.** Let `n ≥ 1`, let `Λ ≤ nV` be finitely generated and let
   `1 ≤ i ≤ n`. Suppose there is a continuous `h : C^n -> Z` with
   `c_{λ,i}(y) = h(λ y) - h(y)` for all `λ ∈ Λ`, `y ∈ C^n`.
   Then `Λ` is isomorphic to a subgroup of `(n-1)V`. For `n = 1`, `Λ` is finite.
2. **Rank reduction for Kazhdan subgroups.** For `n ≥ 1` let `(K_n)` be the statement
   "every Kazhdan subgroup of `nV` is finite", and `(Q_n)` the statement "for every Kazhdan
   `Λ ≤ nV` some coordinate cocycle `c_{·,i}|_Λ` is a continuous coboundary". Then
   `(K_n) ⟺ (K_(n-1)) ∧ (Q_n)`, with `(K_0)` trivially true.
3. **Shape of an infinite Kazhdan subgroup.** If `2V` contains an infinite Kazhdan subgroup
   `Λ`, then neither `c_{·,1}|_Λ` nor `c_{·,2}|_Λ` is a continuous coboundary. More generally,
   a minimal-rank infinite Kazhdan subgroup of any `nV` has no continuously straightenable
   coordinate.

## Consequences

- **The (Q_n) hole is one coordinate at a time.** Item 4 of
  `brin-thompson-torsion-has-clopen-fixed-sets` needs one continuous `β : C^n -> Z^n` for all
  coordinates at once; `(Q_n)` needs one scalar `h` for one coordinate of one's choice.
  By item 2 and `thompson-v-has-haagerup-property` (`K_1`), `(Q_2)` alone is equivalent to
  finiteness of Kazhdan subgroups of `2V`.
- **Where the Robertson–Steger host escapes (remark, not load-bearing).** The refuting host of
  `af-by-z2-ample-groupoid-full-group-contains-infinite-kazhdan` has a `Z^2` cocycle with AF
  kernel, but no product decomposition in which one factor carries a coordinate with an AF
  skew product *and the other factor is again a full group of the same type*. That is exactly
  what item 1 uses: `ker c_i ≅ (AF skew product of G_2) × G_2^(n-1)`, and the second factor
  is the groupoid of `(n-1)V`.
- **What is not reached.** Bounded `c_{·,i}|_Λ` does not obviously give a *continuous* `h`:
  the natural transfer `max_λ (-c_{λ,i})` is only lower semicontinuous when `Λ` is infinite.
  The measure-preserving part `{g : Σ_i c_{g,i} ≡ 0}` of `2V` is not reduced by item 1.
