---
rg: 2
id: hyperbolic-cone-matching-holds-off-the-branch-locus
kind: claim
title: In a hyperbolic group every element maps all sufficiently deep atoms around a non-branch horofunction onto atoms; so the finitely generated nucleus-tile operad of the BBMZ host has Thumann's degree bound for free, and its square filling can fail only over the branch locus, and not at all if the non-surjective part of the nucleus automaton has no cycle
distinct_from:
  finite-germ-extensions-with-singular-blocks-are-f-n: that closes the germ-local route and names the shadow operad; this checks Thumann's hypotheses (VE) and square filling for the finitely generated version, and pins the one remaining gate to a finite automaton test.
  thumann-finiteness-without-finite-type: that removes finite type in favour of the connectivity condition (G); here (G) is not needed once the automaton test passes, because the spine is then finite.
---

**Status.**
- **ESTABLISHED (lane proof, not reviewed):** Theorem 1, the degree bound (VE), the finiteness
  of the transformations, and the localization of square-filling failures to the branch locus.
- **Lane proof sketch:** square filling under (C) and finite type under (C).
- **OPEN:** whether (C) holds for any non-free hyperbolic group, and color-tameness. No
  computation was run, and no priority is claimed.

## Setting

- `G` is hyperbolic, `X = ∂_h G`, and `φ : X → ∂G` is the Webster–Winchester map. A point
  `y ∈ X` is *non-branch* if `φ^{-1}(φ(y)) = {y}`. For `H = G*Z` the same notions apply on
  `∂_h H`.
- Fix a system of addresses. `Nuc` is the finite nucleus of `Γ_h = [[H | ∂_h H]]`.
- The *nucleus automaton* has states `p ∈ Nuc` and edges `p →_e p|_e`.
- `Nuc^× = {p : Im p` is a whole cone`}` is the set of surjective states, and `N' = Nuc ∖ Nuc^×`.
- **(C)** means that the automaton restricted to `N'` has no directed cycle.

## Theorem 1 (cone matching off the branch locus)

Let `g ∈ G` and let `y ∈ X` be non-branch. There is `n_0` such that, for every `n ≥ n_0` and
every `D ∈ 𝒜_n` with `y ∈ ∂D`, the set `gD` is an atom `D' ∈ 𝒜_{n−b}`. Here
`b = h_{gy}(g) − h_{gy}(1) ∈ [−|g|, |g|]`, and consequently `g∂D = ∂D'`. In addresses, the
local actions of `g` along `y` are eventually in `Nuc^×`.

**Proof.** Put `ξ = φ(y)`, and let `γ` be a geodesic ray from `1` to `gξ`. Let `W_m` be the ball
of radius `R' = R'(δ)` about `γ(m)`.

1. **The two distance functions differ by a constant near the front.**
   - Claim: there is `M` with `d(g, z) − d(1, z) = b` for all `m ≥ M` and all `z ∈ W_m`.
   - Otherwise there are `z_m ∈ W_m`, `m → ∞`, violating it. They converge to `gξ` in
     `G ∪ ∂G`, and a subsequence converges in the horofunction compactification to some `η`
     with `φ(η) = gξ`.
   - Since `gy` is the only point over `gξ`, `η = gy`. So the integers
     `d_{z_m}(g) − d_{z_m}(1)` converge to `b`, and eventually equal it. This is a contradiction.
2. **The balls agree on the window.** Put `m = n − b`. Then `gB_n ∩ W_m = B_m ∩ W_m`, and on
   that set the functions `d_x` seen from `gB_n` and from `B_m` are the same.
3. **The visible sets lie in the window.** Let `D'` be the `B_m`-atom with `gy ∈ ∂D'`, and let
   `x ∈ gD ∪ D'`. Then the sets
   `V(x, B_m)`, `V(x, gB_n) = gV(g^{-1}x, B_n)`, `V(D')` and `gV(D)`
   all lie in `W_m`, for `R'` a constant depending on `δ`. The reasons:
   - item 1 of `horofunction-atom-configurations-have-finitely-many-types` puts `N(D)` near
     `γ_ξ(n)` and `N(D')` near `γ(m)`;
   - thin triangles `(1, g, x)` put the crossing of `[1, x]` with `S_m` near the crossing of
     `[g, x]` with `gS_n`;
   - `gγ_ξ(n)` is at distance `m` from `1` by item 1, and it is `8δ`-close to `γ`.
4. **Conclusion.**
   - BBMZ `prop:PropertiesSets`(iv) applies with `U = B_m ∩ W_m`, and its translate by `g` applies
     to atoms of `gB_n`.
   - They give `x ∈ D' ⟺ d_x ≡ d_{D'}` on `U`, and `x ∈ gD ⟺ d_x ≡ d_{gD}` on `U`.
   - The approximants of `gy` lie in both sets, so `d_{gD} = d_{D'}` on `U`. Hence `gD = D'`.

   The address statement follows because `∂D` and `∂D'` are cones. `∎`

**Corollary.**
- Every infinite path of the nucleus automaton that stays in `N'` is realized only along
  branch points.
- (C) holds automatically when `φ` is injective. This includes free groups on a basis, and more
  generally every `G` with totally disconnected `∂G` and `∂_h G = ∂G`.

## The nucleus-tile operad and Thumann's hypotheses

**The operad `𝒪_Nuc`.**
- **Colours.** The nodes of the type graph (cones `C_v`) together with the finitely many shapes
  `T_p = Im p`, `p ∈ Nuc`.
- **Generating operations:**
  - (i) the canonical split of `C_v` into its child cones;
  - (ii) for each `p`, the induced split `T_p = ⊔_e L_{p̄(e)} T_{p|_e}`;
  - (iii) for each `p`, the insertion `C_w = T_p ⊔ (the maximal cones of C_w ∖ T_p)`.
- **Transformations.** The finite groupoid of maps `p'^{-1}p` with `Im p = Im p'`, together with
  the finite atom automorphism groups.

**Facts.**
1. **(VE) holds.** `𝒪_Nuc` is finitely generated, so it has finitely many very elementary classes,
   of degree at most
   `m_V = max(max out-degree, max_p (#complement cones of T_p) + 1, max_p out-degree of p)`.
   This is Thumann's `finitely generated`, Def. `26536`. No connectivity input is needed.
2. **The transformations** form a finite groupoid, which is `F_∞^+`.
3. **Square filling fails only over branch points** (lane proof).
   - Two pieces around a point `ζ` have common descendants exactly when the transition germ `k`
     between their structures maps some small cone around the point onto a cone. The transition
     is a composite of nucleus maps and similarities, which is locally an element of `H`.
   - If either piece has a cone descendant around `ζ`, the insertions (iii) copy the other side.
     This is after refining the other side below the complement depth `c` of the tile shapes.
   - By Theorem 1, `k` has a cone-matching cone around every non-branch point.
4. **Under (C), square filling holds** (lane proof sketch). Along every point, the local actions
   of every transition enter `Nuc^×` within `d_0` steps, where `d_0` is the longest path in `N'`.
   So matching succeeds everywhere, and compactness gives a common refinement. Equalization
   follows from injectivity (Thumann's remark for operads of maps).
5. **Under (C), `𝒪_Nuc` has finite type** (sketch). Minimal common refinements of pairs involve
   pieces within depth `d_0 + c` of the pieces refined. So the iteration of Thumann's
   Construction `45209` stays among dissections of bounded depth over finitely many colours, and
   the spine is finite. Then (G) is vacuous.
6. **Consequence.** Under (C), and if `𝒪_Nuc` is color-tame (Def. `77101`, open here),
   Thumann's Theorem `41762` makes `π_1(𝒪_Nuc, E)` of type F_∞. `π_1(𝒪_Nuc, E) = Γ_h` if every
   element of `Γ_h` is a fraction of `𝒪_Nuc`-dissections. That holds after refining below the
   complement depth; sketch as in 3. So `Γ_h`, and the twisted Brin–Thompson envelope `SV_{Γ_h}`,
   would be F_∞ (via `twisted-bt-of-full-contracting-rsg-inherits-f-n-from-rsg-family`). That
   answers the F_∞ half of Zaremsky's question for `G`.

**The all-partitions shadow operad** (colours atom types, operations all partitions into
`H`-translates of shadows) is the wrong choice.
- Square filling is free there.
- But (VE) needs a bound on partitions with no proper coarsening, and that is the same
  cone-matching input in disguise. So nothing is gained over `𝒪_Nuc`, and (G) would be needed
  on top.

## Lesson for general BH

- **Hyperbolicity makes every element finitary where the Cantor model is injective.** Away from
  the branch locus, deep atoms map onto atoms. The reason is that the difference of two distance
  functions is eventually constant on the front of a ball.
- **So finiteness trouble for hyperbolic full groups lives only on the branch locus.** There,
  several horofunctions over one boundary point give the front two competing shapes.
- **The whole F_∞ question becomes a finite automaton test.** It is whether the non-surjective
  part of the nucleus automaton has a cycle. That condition is decidable from finite data (type
  graph plus nucleus), and it is the only input-dependent gate left on this route, apart from
  color-tameness.
- **The best finiteness engine here is the finitely generated tile operad.** It gets Thumann's
  (VE) for free and reduces square filling to cone matching; the Cuntz and (G) tools are
  unnecessary on this route.

## Next

- **Run the test on one example.** For a closed surface group with the standard presentation,
  compute the type graph, the nucleus automaton and `N'`, and test (C). This is a finite
  computation, suitable for one Slurm msismall job, and the natural calibration for Kazhdan
  inputs.
- **If (C) fails,** find the cycles. They sit over branch points, by Theorem 1. Then either add
  "configuration insertions" indexed by the finitely many configuration types, to restore
  square filling, or prove Thumann's (G) for the enlarged operad.
- **Check color-tameness** of `𝒪_Nuc`.
