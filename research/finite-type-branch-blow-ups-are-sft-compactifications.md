---
rg: 2
id: finite-type-branch-blow-ups-are-sft-compactifications
kind: claim
title: Finite-type branch blow-ups are exactly the SFT compactifications of the tree-gluing node, their engines are its tree gluing over Z/2 * S, and for hyperbolic S (Kazhdan ones included) the distance-gradient SFT has a unique seed, reducing (IE′) to one horofunction lemma
requires:
  - stabilizer-engines-embed-in-every-branch-compactification
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
---

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-18; elementary; not reviewed):
- parts 1–3;
- part 4(a), the unique seed;
- part 4(b), the reduction.

**OPEN:** the lemma (HL) of part 4(c) in general.

**PROVED for `F_n` (free basis) and for closed surface groups `Γ_g` (standard generators)** in
`horofunction-lemma-holds-for-free-and-surface-groups`. So for these groups the seed orbit is dense in `Y_R`, and
(IE′) holds.

**Notation.** As in `stabilizer-engines-embed-in-every-branch-compactification` (the parent): `D = Z/2 * S`,
S-compactifications `K = S ⊔ ∂`, engines `Ω^K` and `F_S^K`. An *SFT compactification* `(Y, π)` is as in
`tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts` (the gluing node):
- (C1) the cylinder of the seed `π` is `{y_*}`, with `Stab(y_*) = 1`;
- (C2) `Y` is the orbit closure of `y_*`.

`S` is finitely generated, and `|S| > 2`.

## 1. (IE′) is the gluing node's notion without rigidity

An S-compactification `K` is of finite type (parent, part 3) iff it is conjugate to an SFT compactification.

- (⇐) The cylinder of `π` is clopen and equals `{y_*}`, so `y_*` is isolated. Hence `S·y_*` is open,
  discrete and dense (C2), and `s ↦ s·y_*` is injective (C1).
- (⇒) If `x` is isolated in the SFT `\overline{Sx}`, some cylinder `[x|_F]` equals `{x}`. For
  `B_R ⊇ F`, the pattern `π = x|_{B_R}` satisfies (C1), and (C2) holds by definition.

**So:** (IE′) for `S` is the statement "S has an SFT compactification", and `S ∈ 𝒞` (the gluing node's
class) is (IE′) plus quantum rigidity. The open premise (★𝒞) of
`decidable-groups-embed-in-rigid-sft-compactification-groups` asks for (IE′) with rigidity, over an fp
overgroup of the input.

## 2. The blow-up engine is the gluing node's tree gluing

Let `(Y, π)` be an SFT compactification of `S`, and let `(Y_1, π_1)` be the one-orbit compactification of
`Z/2`. Let `X` be the tree gluing (rules R1, R3) of the gluing node for `Λ_0 = S`, `Λ_1 = Z/2`. Then there is
a `D`-equivariant homeomorphism `Φ : X → Ω^Y`.

**Proof.**
- *Flows.* Orient `T` as in the gluing node. Every element node has out-degree 1. A piece has out-degree 1
  if it is seeded (towards its seed), and 0 otherwise. Z/2-pieces are always seeded, so the only sinks are
  unseeded S-pieces. A forward path never backtracks: `λ → P → μ` forces `μ ≠ λ`, since `P` is not seeded
  at `λ`. So each forward path ends at a sink or converges to an end.
- *One target.* On the geodesic between two nodes no vertex has two outgoing path edges. So any two forward
  paths merge, and every `x` has one target: an end, or a sink `P = gS`.
- *Definition of Φ.* Put `Φ(x)` equal to that end, or to the label `h ↦ x_0(gh)` of the sink. That label is
  a seedless point of `Y`, i.e. a point of `∂_P`.
- *Φ is a bijection.* The target determines `x`:
  - every seeded S-piece carries its unique seeded point by (C1), seeded where the flow leaves it;
  - every Z/2-piece is determined by its seed;
  - the sink carries `Φ(x)`.
  Conversely, every end and every `∂_P`-point arises: R1 and R3 hold by construction.
- *Continuity.* A piece `gS` is seeded at `gs` iff the target lies in the shadow through the edge `gs`, and
  seeded points correspond to `s ∈ S ⊆ Y`. So `Φ^{-1}(N(v,U))` is the set where the label of `v` lies in `U`,
  and `Φ^{-1}(Sh(H))` is fixed by the orientation of one edge. Both are clopen.
- *Conclusion.* `Φ` is a continuous bijection from a compact space to a Hausdorff one, hence a
  homeomorphism, and it is `D`-equivariant.

**Consequence.**
- By the gluing node, `D ⋉ Ω^Y` is minimal and topologically free.
- It is `D`-quantum rigid whenever `Y` is.
- When `S` is finitely presented, `F_S^Y` is the full group of a minimal, topologically free SFT over the fp
  group `Z/2 * S`.

So a *rigid* finite-type blow-up is literally a (★′) instance over `Λ_0 = Z/2 * S`, with the input carried by
a vertex group of the acting group. Track C, repaired at the emitter, is the gluing node's route with
`Λ_1 = Z/2` instead of `Z`.

## 3. What one-endedness forces

Let `S` be one-ended and `K` any S-compactification. Then:
- (a) every S-invariant clopen subset of `∂` is `∅` or `∂`;
- (b) (parent, part 2) if `S` has no proper finite-index subgroup, `∂` is infinite unless `K = S⁺`.

**Proof of (a).** Let `C ⊆ K` be clopen with `C ∩ ∂` S-invariant, and put `W = C ∩ S`.
- `tC Δ C` is clopen and misses `∂`, so it is a finite subset of `S`. Hence `tW Δ W` is finite, and `W^{-1}` is
  almost invariant under right multiplication.
- One end then makes `W` finite or cofinite.
- Every neighbourhood of a point of `∂` meets `S` in an infinite set. So `W` finite gives `C ∩ ∂ = ∅`, and
  `W` cofinite gives `C ⊇ ∂`.

A one-ended input therefore needs a remainder that is infinite and clopen-indecomposable. The remainder of the
`Z²` corner compactification (parent, 3c) is such a remainder.

## 4. Hyperbolic groups: a unique seed from Cannon's cone types

Let `S` be δ-hyperbolic for a finite symmetric generating set `Σ`. Let `k = k(δ)` be the tail length in
Cannon's cone-type lemma (Bridson–Haefliger III.Γ.2.18):

> the cone type `C(g) = {u : |gu| = |g| + |u|}` is determined by the k-tail `{u ∈ B_k : |gu| < |g|}`.

By left invariance the same holds for cones and tails with respect to any base point `q`.

**The distance-gradient SFT.**
- A function `f : S → Z` modulo constants is coded by its gradient `∇f(g) = (f(gσ) − f(g))_{σ∈Σ}` in
  `{−1,0,1}^Σ`. For the relators of a finite (Dehn) presentation, the cocycle condition is local.
- Fix `R ≥ k + 2`. Let `Y_R` be the SFT of gradient fields whose restriction to every ball `B_R(v)` equals,
  up to a constant, the restriction of some `d(·,q)`. Up to constants there are finitely many such patterns.
- Put `y_* = ∇d(·,1)`, so `g·y_* = ∇d(·,g)`. The seed is `π = y_*|_{B_R}`.

**(a) Unique seed.** The cylinder of `π` in `Y_R` is `{y_*}`, and `Stab(y_*) = 1`.

*Proof.* Let `f ∈ Y_R` with `∇f|_{B_R} = π`, normalized so that `f = |·|` on `B_R(1)`. We induct on `n ≥ R`
that `f = |·|` on `B_n(1)`.
- Let `|g| = n + 1`, and let `g''` be the point at distance `R − 1` from `g` on a geodesic from `1` to `g`.
  Then `B_{R−2}(g'') ⊆ B_n(1)`, and by the `Y_R` rule `f = d(·,q) + c'` on `B_R(g'')` for some `q`.
- On `B_k(g'')` both `d(·,q) + c'` and `|·|` equal `f`. So the k-tails of `g''` with respect to `q` and to
  `1` coincide, and by Cannon so do the cones.
- Write `g = g''u`. Then `u ∈ C_1(g'') = C_q(g'')` and `|u| = R − 1`, so
  `f(g) = d(g'',q) + |u| + c' = f(g'') + |u| = |g|`.

Translates of `d(·,1)` are distinct, so the stabilizer is trivial. ∎

**Hence:**
- `y_*` is isolated in the SFT `Y_R`.
- `K_h := \overline{S·y_*}`, which does not depend on `R`, is an S-compactification. Its remainder is the
  horofunction boundary `∂_h` of the Cayley graph, which is infinite when `S` is non-elementary.
- By the parent's part 1, `F_S ↪ F_S^{K_h}`.

**(b) Reduction of (C2) to rays.** Let `f ∈ Y_R` be outside the seed orbit, and let `γ` be an f-descending path from `1`. Such a path
exists: a point that is not a local minimum has a descending neighbour, and a local minimum is a seed by (a).
- `γ` is a geodesic, since `f` is 1-Lipschitz and drops by exactly 1 per step.
- `b_γ(h) = lim_m (d(h, γ_m) − m)` exists and is eventually constant for each `h`: the sequence is integral,
  non-increasing and `≥ −|h|`.
- Always `f − f(1) ≤ b_γ`, since `f(h) ≤ f(γ_m) + d(h,γ_m)`.
- If equality holds, pick `m` with `d(·,γ_m) − m = b_γ` on `B_n(1)`. Then `f|_{B_n} = d(·,γ_m)|_{B_n} + c`
  for every `n`, so `f ∈ K_h`.

**(c) (HL), OPEN.** For every `f ∈ Y_R` and some f-descending ray `γ`, `f − f(1) = b_γ`. Equivalently,
`Y_R = K_h`, i.e. (C2).
- By (b), (HL) makes `(Y_R, π)` an SFT compactification, so `K_h` is of finite type and (IE′) holds for `S`.
- **Checked at source (09-18): Coornaert–Papadopoulos do NOT prove (HL).** The paper is M. Coornaert and
  A. Papadopoulos, "Horofunctions and symbolic dynamics on Gromov hyperbolic groups", Glasgow Math. J. 43
  (2001) 425–456, doi:10.1017/S0017089501030063, read in the published PDF.
  - *Their horofunctions are a different class.* Def. 2.1 defines horofunctions by two global conditions,
    ε-convexity and the distance-like property `h(x) = λ + dist(x, h^{-1}(λ))` for all `λ ≤ h(x)`. So
    `d(·,g)`, which is bounded below, is not one. `Φ_0` is the set of integral horofunctions modulo constants.
  - *Their main theorem codes a single map, not the group action.* The Theorem on p. 426 says that
    `(Φ_0, α)` is topologically conjugate to a one-sided subshift of finite type. Here `α(φ) = a^{-1}φ`,
    with `a` the smallest generator satisfying `h(Id) − h(a) = 1`.
  - *Their local-to-global step lives on a tube.* The SFT `Σ(∞)` of consistent sequences (Def. 6.7,
    Thm. 6.13) records restrictions of genuine horofunctions to a tube `N(r, R_0)` around one gradient ray.
    §7–8 build a horofunction from a consistent sequence.
  - *Two facts we use.* Prop. 3.4: `φ(x, r(t)) = dist(x, R_{φ,t})`, where
    `R_{φ,t} = {z : φ(r(t),z) = 0} ∩ B(r(t),16δ)`. Cor. 3.6: a horofunction is determined by its values on
    the 16δ-neighbourhood of one ray to its point at infinity.
  - *What (HL) needs instead.* Here the local states are restrictions of distance functions, the group is
    the acting object, and the conclusion must be a limit of distance functions. None of this is in the
    paper.
  - *Consequence (lane proof).* Pointwise limits of normalized `d(·,g_n)` are integral CP horofunctions, so
    `∂_h ⊆ Φ_0`. The distance-like property passes to the limit on balls, and ε-convexity is closed under
    limits (distance functions are ε-convex, CP ref. [7], Ch. 3, Lemma 3.2). Prop. 3.4 gives only
    `h ≤ b_r` for a CP horofunction `h` and its gradient ray `r`, the same inequality as in (b). So
    `Φ_0 = ∂_h` is itself open.
  - (HL) is PROVED for free groups and closed surface groups (`horofunction-lemma-holds-for-free-and-surface-groups`:
    wall orientations, Helly in `H²`, and a descent lemma bounding minimal pointing-away wall pairs). In general
    it is OPEN. bh-g2-buildings, which needs the same lemma for its hyperbolic compactification, is
    proving it directly (notes exchanged on the boards).
- Calibration: for `Z²` with the standard generators, `Σ`-tails also determine cones, part (a) goes through,
  and `K_h` is the ℓ¹ horofunction compactification. That one is of finite type (quadrant sign patterns).

## Answer to the Kazhdan test

- **Kazhdan is no obstruction to a unique seed.** Uniform lattices in `Sp(n,1)` (`n ≥ 2`) and Żuk's random
  groups are infinite, hyperbolic and Kazhdan.
  - For them `Y_R` is an SFT with an isolated seed of trivial stabilizer (4a).
  - `K_h` is a non-finite-remainder compactification with a dense seed orbit, as part 3 demands of
    one-ended groups.
  - Modulo (HL) it is of finite type.
- **It does not reach the hard inputs.** Hyperbolic groups are never simple, and the simple Kazhdan inputs
  `H_Γ` of `decidable-host-classes-reduce-to-canonical-kazhdan-groups` are not hyperbolic.
  - The proof of 4(a) uses only one property, (TP): cones with respect to every base point are determined
    by bounded tails.
  - So (IE′) for an input reduces to (TP) plus (HL) for some Cayley graph of it, or of an overgroup, to
    which the blow-up can be transported.
  - Whether any `H_Γ`, or an fp overgroup of one, has a Cayley graph with (TP) is open.

## Lesson for general BH

- The emitter repair and the rigid-compactification route are the same object. A finite-type branch blow-up
  is exactly an SFT compactification, and its engine is the free-product tree gluing over `Z/2 * S`. So
  Track C, repaired, IS Track A′ with the input as a vertex group, and the only extra gate is rigidity.
- For the seed, the natural source is metric: a distance function is determined by its local gradient
  pattern once cones are determined by bounded tails (Cannon). That gives a unique seed for every
  hyperbolic group, Kazhdan or not.
- So Kazhdan-ness blocks only finite remainders. For one-ended inputs the remainder must be an infinite,
  clopen-indecomposable horofunction-type boundary.
- The live question moves from "can an emitter be finitely presented?" to "does the input have a Cayley
  graph whose cones are locally determined?", i.e. (TP) + (HL). That fails for the known non-hyperbolic
  simple Kazhdan inputs, which points the remaining work at overgroups with (TP).
- Checked at source: Coornaert–Papadopoulos's symbolic coding is one-sided, for the single map `α`, and
  its local-to-global step lives on a tube around one gradient ray. The two-sided group SFT with a seed
  needs a different local-to-global statement, (HL). The citation that was "expected" to close it does not.
