---
rg: 2
id: rational-affine-rn-groups-are-not-k-graph-full-groups
kind: claim
title: Every continuous Z-cocycle on the germ groupoid of Aff(Z[1/pm], U) acting on Z_p is a multiplier character plus a coboundary, and its translation core Z[1/m] x Z_p has H_1 = Z[1/m]; so no finite k-graph groupoid is Kakutani equivalent to it, and V_3(BS(1,2)) is the full group of no finite k-graph, for any k
distinct_from:
  dyadic-affine-germ-groupoids-are-not-k-graph-groupoids: that uses the prime-support property of k-graph homology and cannot see V_3(BS(1,2)), whose homology (Z/2, Z/2, 0) is that of the one-vertex (3,3) 2-graph; this uses the degree cocycle and the AF core, an invariant finer than homology, and covers every prime p and every m > 1 at once.
  s-arithmetic-affine-rn-groups-are-k-graph-full-groups: that builds k-graph models over F_q(t); this proves that the analogous groupoids over Q never have one, and locates the difference in one fact (the translation group is locally finite in positive characteristic and contains Z in characteristic 0).
  basilica-rn-group-is-not-a-k-graph-full-group: that uses rational homology; the groupoids here are rationally acyclic in many cases (for example V_3(BS(1,2)) and V_2(BS(1,3))) and still excluded.
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/one_vertex_digit_search.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-one-vertex-digit-search.txt
---

**ESTABLISHED (proof in `rational-affine-rn-groups-are-not-k-graph-full-groups-proof`; lane proof, w14-101; not
independently reviewed).** Imported: Matui's homology of AF groupoids (`H_n = 0` for `n ≥ 1`), Morita (Kakutani)
invariance of ample-groupoid homology (Crainic–Moerdijk), the dimension group `Z[1/p]` of the `p`-adic odometer,
and part 1 (rigidity: a full-group isomorphism is a groupoid isomorphism) of
`basilica-rn-group-is-not-a-k-graph-full-group`. The rest is proved in full.

## Setting

- `p` is a prime and `m > 1` is an integer prime to `p`. Put `R = Z[1/pm]` and `B = Z[1/m] = R ∩ Z_p`.
- `U ≤ R^×` is torsion-free and finitely generated, with `v_p(U) ≠ 0`.
- `𝒢 = 𝒢_{p,m,U}` is the groupoid of germs of the maps `x ↦ ux + b` (`u ∈ U`, `b ∈ R`) at points `ω ∈ Z_p` with
  `uω + b ∈ Z_p`. A germ determines its affine map, so `u : 𝒢 → U` is a continuous homomorphism (the
  **multiplier**).
- **Translation core.** `ker u` is the transformation groupoid `B ⋉ Z_p` of the translation action.
- **Main example.** `BS(1,2) = ⟨x + 1, 2x⟩` acts on `Z_3`, the ternary tree, and `𝒢_{3,2,⟨2,3⟩}` is the germ groupoid
  of `V_3(BS(1,2))`, i.e. of `Aff(Z[1/6], ⟨2, 3⟩)` on `Z_3` (as in
  `dyadic-affine-germ-groupoids-are-not-k-graph-groupoids`, part 4). `V_2(BS(1,r))`, `r` odd, `|r| ≥ 3`, is
  `𝒢_{2,|r|,⟨2,r⟩}`.

## Statement

1. **Cocycle rigidity.** Every continuous homomorphism `ψ : 𝒢 → Z` is `χ ∘ u + ∂g` for a homomorphism
   `χ : U → Z` and some `g ∈ C(Z_p, Z)`. So `H^1(𝒢; Z) = Hom(U, Z)`.
2. **The core is not AF.** `H_1(B ⋉ Z_p) ≅ Z[1/m] ≠ 0`.
3. **AF-core obstruction.** Let `Λ` be a finite `k`-graph with no sources, any `k ≥ 1`. Then `𝒢` is **not**
   Kakutani equivalent to `G_Λ`.
   - The degree cocycle `d : G_Λ → Z^k` has AF kernel. Transported to `𝒢` it must be `χ ∘ u` up to a coboundary
     (part 1), with `χ` injective, because the skew product by `d` is principal.
   - The skew products by cohomologous cocycles are isomorphic. The one by `d` is Kakutani equivalent to an AF
     groupoid, and the one by `χ ∘ u` is Kakutani equivalent to copies of `B ⋉ Z_p`. Part 2 separates them by `H_1`.
4. **Consequences.**
   - **`V_3(BS(1,2))` is the full group of no finite `k`-graph with (H), for any `k`.** This decides the case left
     open by `dyadic-affine-germ-groupoids-are-not-k-graph-groupoids`. The homology `(Z/2, Z/2, 0)` agrees with the
     one-vertex `(3,3)` 2-graph, but that 2-graph has AF degree core, and `𝒢` has core with `H_1 = Z[1/2]`.
   - The same holds for every `V_p(Z[1/m] ⋊ U_0)` with `U_0 ≤ Z[1/m]^×` torsion-free, `m > 1`, `p ∤ m`. Its germ
     groupoid is `𝒢_{p,m,⟨p⟩ × U_0}`. This re-proves the `V_2(BS(1,r))` case with a single argument.
   - Together with the `m = 1` odometer case (excluded rationally in `basilica-rn-group-is-not-a-k-graph-full-group`),
     **no Roever–Nekrashevych group of an `S`-arithmetic affine group over `Q` with torsion-free units is a finite
     `k`-graph full group**.

## Where the function-field case differs

Over `F_q(t)` the translation group `B = F_q[t][1/(p_1⋯p_{k-1})]` is locally finite, so `B ⋉ F_q[[t]]` is AF. Part 3
then raises no objection, and indeed `s-arithmetic-affine-rn-groups-are-k-graph-full-groups` builds the models: its
degree cocycle is exactly the multiplier. Over `Q`, `B ⊇ Z` acts as an odometer, whose `H_1 = Z` survives in the
direct limit as `Z[1/m]`. **The obstruction is characteristic 0 itself**, and not the archimedean place (the
heuristic in the remarks of `s-arithmetic-affine-rn-groups-are-k-graph-full-groups`).

## What this closes, and what it leaves

- **Closed.** For these groups, the `k`-graph route to `F_∞` through Li's theorem
  (`li-finite-k-graph-full-groups-are-f-infinity`) is closed over `Q`, for every model.
- **Calibration.**
  - The lamplighter 2-graph and the `F_q(t)` models have multiplier = degree, with AF translation core. They are
    consistent with part 3.
  - `one_vertex_digit_search.py` searches directly for one-vertex 2-graph digit sets `(E, F)` in
    `Aff(Z[1/6], ⟨2,3⟩)`. It finds none (1,346 admissible pairs tested). This is consistent with part 3, which forbids all of them.
- **Open.** What remains are the finiteness properties (`F_n`) of `V_p(Z[1/m] ⋊ U_0)` over `Q`. They need a
  different complex: a Stein–Farley complex decorated by the Bruhat–Tits trees at the primes dividing `m`, as in
  `rn-lamplighter-is-a-function-field-stein-group`, which does not go through `k`-graphs.
