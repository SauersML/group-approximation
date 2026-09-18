---
rg: 2
id: thompson-f-two-transitive-binary-colourings-force-regular-closed
kind: claim
title: In a 2-transitive action of Thompson's group F, bad irrational points are dense in every disagreement set, and a two-colour bad orbit forces an interior D_0 to be a regular closed set with no gap between two interval components
distinct_from:
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim gives the orbit of D_0, splicing at gaps and clopen self-similarity; this claim uses them to prove density of a bad orbit in each disagreement set and, for two colours, a symmetric-difference rule and a complement duality
  thompson-f-two-transitive-irrational-orbit-colorings: that claim defines the colourings and proves that a bad orbit meets every disagreement set; this claim upgrades meeting to density and adds the sum rule when the stabilizer has exactly two orbits on a bad irrational orbit
  thompson-f-two-transitive-disagreement-sets-have-no-interior: that claim is the open hole excluding interior; this claim excludes only the sub-case where some bad irrational orbit carries two colours and D_0 is not regular closed or has a gap bounded by two interval components
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim is the Cantor half of the dichotomy; nothing here constrains the Cantor case
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of
distinct points. Fix `ω`, put `H = F_ω`, and use `G_x`, `D(ω_1,ω_2)`, `D_0`,
bad orbits and the colourings `c_{ω_1}` of an irrational orbit `O` exactly as
in `thompson-f-two-transitive-disagreement-sets-are-self-similar` and
`thompson-f-two-transitive-irrational-orbit-colorings`. Call a bad irrational
orbit `O` **binary** if `H` has exactly two orbits on `O`, that is, if the
partition `P_O` has exactly two parts.

1. (Density.) For every bad irrational orbit `O` and every pair
   `ω_1 ≠ ω_2`, the set `O ∩ D(ω_1,ω_2)` is dense in `D(ω_1,ω_2)`. Hence
   `D(ω_1,ω_2) = cl{ y ∈ O : c_{ω_1}(y) ≠ c_{ω_2}(y) }`.
2. (Unique splicing.) If `D(ω,α) = D(ω,α') = C_1`,
   `D(α,ω') = D(α',ω') = C_2` and `C_1 ∩ C_2 = ∅`, then `α = α'`.
3. (Sum rule.) If some bad irrational orbit is binary, then for all
   `ω_0, ω', ω''`,
   `D(ω',ω'') = cl( D(ω_0,ω') Δ D(ω_0,ω'') )`,
   and `ω' ↦ D(ω_0,ω')` is injective on `Ω`.
4. (Interior case.) Suppose some bad irrational orbit is binary and `D_0`
   has nonempty interior. Then:
   - (a) `D_0` is regular closed: `D_0 = cl(int D_0)`;
   - (b) no gap of `D_0` is bounded by two nondegenerate components: if
     `[s,a]` and `[b,t]` are components of `D_0` with `s < a < b < t`, then
     `(a,b)` meets `D_0`, and in fact meets `int D_0`;
   - (c) (complement duality) if `E` is a translate of `D_0` and `c < d` are
     interior points of `E` lying in different components of `E`, then
     `[c,d] ∖ int E` is a translate `hD_0`, `h ∈ F`.

**What this kills.** In the binary sub-case of
`thompson-f-two-transitive-disagreement-sets-have-no-interior`, every model
of `D_0` of either of two kinds is excluded:
- models with a pattern "interval, gap, interval", which (b) forbids;
- models with a Cantor stretch, meaning an open set that meets `D_0` but
  contains no interval of `D_0`, such as an interval disjoint union a Cantor
  set, which (a) forbids.

What survives is the **checkerboard type**: a regular closed set in which
every gap has at least one endpoint that is a limit of interval components,
and whose complement between two interior points in different components is
again a translate of it, so it satisfies the same condition.

Item (c) has bite. A middle-thirds Cantor set `C` with a closed interval
`[p,q]` placed strictly inside each gap `(u,v)` satisfies (a) and (b). But its
complement between two interior points is `C` together with the intervals
`[u,p]` and `[q,v]`. That set has the gap `(p,q)` between two interval
components, so (b) and (c) together exclude the model.

The closure of the union of the odd-level gaps of `C` passes (a) and (b), and
it passes (b) for its complement too. Its complement between two interior
points is the closure of the even-level gaps, which has the same shape. So
these tools alone cannot close the hole.

**Where it dies.**
- With three or more colours on every bad irrational orbit, item 3 fails.
  `c' ≠ c''` no longer follows from exactly one of `c' ≠ c`, `c'' ≠ c`. In
  the construction of item 4, `D(fω,ω') ∩ int E` is then uncontrolled.
- For the checkerboard type, the missing input is a way to tell the
  interval components of `D_0` from the gaps of `D_0` by the `F`-action.
  Item 4(c) shows they are exchanged by a translate.
- Nothing here touches case (A), the Cantor case.

Scope: unreviewed; no novelty claimed. The argument uses only the imported
facts named in the proof route.

**Proof:** thompson-f-two-transitive-binary-colourings-regular-closed-proof.
