---
rg: 2
id: k-local-distance-functions-on-hyperbolic-groups-are-global
kind: claim
title: On a δ-hyperbolic Cayley graph a function that is (2δ+4)-locally a distance function is globally a distance function if it has a local minimum, and otherwise an integral Coornaert–Papadopoulos horofunction with one centre, so the horofunction lemma (HL) reduces to CP horofunctions being limits of distance functions
requires:
  - finite-type-branch-blow-ups-are-sft-compactifications
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
distinct_from:
  finite-type-branch-blow-ups-are-sft-compactifications: its part 4(a) proves the unique seed by induction with Cannon's cone types; this reproves it by a target argument with explicit k = 2δ+4, and adds the structure of the seedless points (one centre, fellow-travelling descents, CP horofunction), which is new.
---

**ESTABLISHED** (lane proof, bh-g2-buildings, 2026-09-18; elementary; not reviewed). The lemma (HL)
itself (part 4(c) of `finite-type-branch-blow-ups-are-sft-compactifications`) stays **OPEN**; it is
reduced below.

## Setting

- `Γ` has a finite symmetric generating set `S`. Its Cayley graph is `δ`-thin: in every geodesic
  triangle, points on two sides at equal distance `≤` the Gromov product from their common vertex are
  within `δ` of each other. Such a graph is `δ`-slim, and its geodesic quadrilaterals are `2δ`-slim.
- `f : Γ -> Z` is *k-locally genuine* if for every `g` there is `q ∈ Γ` with
  `f − f(g) = d(·,q) − d(g,q)` on `B_k(g)`. This is the rule of the distance-gradient SFT `Y_R`
  (with `R = k`).
- A *sink* is a local minimum.
- A *descending path* drops `f` by exactly 1 per step. Write `α_λ` for its point at level `λ`.

## Theorem

Let `k ≥ 2δ + 4` and let `f` be k-locally genuine.
- **(0) Local structure.**
  - `f` is 1-Lipschitz, and every descending path is a geodesic.
  - At a non-sink, some neighbour is lower by exactly 1.
  - At a sink `p`, `f = f(p) + d(·,p)` on `B_k(p)`.
- **(1) Fellow travelling.** Let `α, α'` be maximal descending paths from neighbours, or from one
  point. Then `d(α_λ, α'_λ) ≤ 2δ + 4` at every level `λ` where both are defined.
- **(2) One target.** All maximal descending paths of `f` end at the same sink, or all are geodesic rays
  converging to the same `ξ ∈ ∂Γ`.
- **(3) Sink case.** If `f` has a sink `p`, then `f = f(p) + d(·,p)` everywhere. So the seed cylinder of
  `Y_R` is one point with trivial stabilizer.
- **(4) Seedless case.** If `f` has no sink, then:
  - `f` is distance-like: `f(x) = λ + d(x, f^(−1)(λ))` for all `λ ≤ f(x)`;
  - `f` is `4δ`-convex along geodesics: `f(x_t) ≤ ((L−t)/L) f(x_0) + (t/L) f(x_1) + 4δ` on
    `[x_0, x_1]`, where `L = d(x_0,x_1)` and `d(x_0,x_t) = t`.

  So `f` is an integral horofunction in the sense of Coornaert–Papadopoulos (Glasgow 2001, Def. 2.1).

## Proof

**(0).**
- Edgewise 1-Lipschitz gives global 1-Lipschitz, so a path dropping 1 per step is a geodesic.
- At `g`, take the genuine pattern with target `q`. If `q ≠ g`, the first step of a geodesic to `q` drops
  by 1. If `q = g`, then `g` is a sink and `f − f(g) = d(·,g)` on the ball. A sink cannot have `q ≠ g`.

**(1).** Suppose `a, a'` are at the same level with `d(a,a') ≤ E ≤ k`. Take the genuine pattern at
`a`, with target `q`, so `d(a,q) = d(a',q)`.
- **One stretch.** While the paths stay in `B_k(a)` they drop `d(·,q)`, so they are initial segments
  of geodesics `[a,q]` and `[a',q]`. The only sink in the ball is `q`, so both continue until `q`.
- **Thinness.** After `s` steps both points are at distance `d(a,q) − s` from `q`. Since
  `(a|a')_q ≥ d(a,q) − E/2`, thinness gives distance `≤ δ` for `E/2 ≤ s ≤ k − E`, and `≤ 2E` for
  `s < E/2`.
- **Iterating.** Start with `E ≤ 2`. For neighbours at different levels, step once along the higher
  path. Restart every `k − δ` steps from a pair at distance `≤ δ`. This needs `k − δ ≥ δ/2`. The bound
  `max(4, 2δ) ≤ 2δ + 4` holds throughout.

**(2).**
- **Sinks match.** Let `α` end at a sink `p`. The path `α'` cannot stop at a sink `p'` above `f(p)`:
  - `α` passes level `f(p')` within `2δ + 4 ≤ k` of `p'`;
  - on `B_k(p')`, the only point at that level is `p'`;
  - so `α` would pass through the sink `p'` and end there.

  So `α'` reaches level `f(p)` within `2δ+4` of `p`, which forces `α'_(f(p)) = p`.
- **Rays match.** Infinite paths correspond to infinite paths, and by (1) their endpoints in `∂Γ`
  agree.
- **Conclusion.** The target is locally constant, and the Cayley graph is connected.

**(3).** Every descending path from `x` is a geodesic to `p` of length `f(x) − f(p)`.

**(4).**
- **Distance-like.** The descending path from `x` meets every level `λ ≤ f(x)` at distance `f(x) − λ`.
  The reverse inequality is 1-Lipschitz.
- **Setup for convexity.** Let `x_0 … x_L` be the vertices of `[x_0, x_1]`, and let `α^i` be descending
  rays from `x_i`.
  - By (1) along consecutive vertices, `α^0_λ` and `α^L_λ` are within `E_L = L(2δ+4)` of each other.
  - Take `λ < f(x_0) − L − E_L − 2δ`, and consider the quadrilateral `x_0, x_1, α^L_λ, α^0_λ`.
- **Where `x_t` can be close to.** `x_t` is `2δ`-close to one of the other three sides.
  - It cannot be close to the bottom side: there `f ≤ λ + E_L`, while `f(x_t) ≥ f(x_0) − L`.
  - Near `α^0` it gives `f(x_t) ≤ f(x_0) − t + 4δ`.
  - Near `α^L` it gives `f(x_t) ≤ f(x_1) − (L − t) + 4δ`.
- **Conclusion.** The minimum of the two is at most the stated convex combination. `∎`

## Consequences for (HL)

**Update (same day).** (HL) is proved in `hyperbolic-groups-have-sft-horofunction-compactifications`,
by propagating one local target upstream, with no merging. Merging itself fails in some hyperbolic
Cayley graphs (Webster–Winchester). The reduction below is kept as a record.

- **Where the seedless points lie.** Let `Φ_0` be the integral CP horofunctions modulo constants, and
  `∂_h` the horofunction boundary (limits of normalized `d(·,g_n)`). Then:
  - `Y_R ∖ (seed orbit) ⊆ Φ_0` (Theorem (4));
  - `∂_h ⊆ Φ_0` (bh-invent-13, from CP).
- **The reduction.** So **(HL) follows from `Φ_0 ⊆ ∂_h`**: every integral CP horofunction on a
  hyperbolic Cayley graph is a limit of distance functions. Then `Y_R` is the horofunction
  compactification of finite type, and bh-invent-13's (IE′) holds for every hyperbolic group.
- **A sufficient condition: merging.** Suppose any two points have a common descendant: a `z` with
  `f(x) − f(z) = d(x,z)` and `f(y) − f(z) = d(y,z)`. Then `f ∈ K_h`: take `p` a common descendant of
  a ball, so `f = d(·,p) + const` there.
  - Merging holds when the Cayley graph is a tree, since rays to the same end eventually coincide.
  - With (1), merging reduces to pairs at the same level within `δ`, far along the rays.
- **What a counterexample would look like.** Two parallel descending "lanes" at bounded distance with
  no common descendant, such that every ball of radius `R'` still fits one distance function, but some
  larger ball fits none. For `x, y` in different lanes, the defect vector `d(·,p) − f` on the ball would
  then never be constant.
  - (1) shows the lanes stay `2δ+4`-close, so a counterexample lives in a bounded tube around one ray.
  - That tube is the same one on which CP's consistent sequences live (their Thm. 6.13).
- **Merging is sufficient, not necessary.** A limit of `d(·,q_t)` with targets `q_t` equidistant from
  two non-merging lanes would lie in `K_h` without merging. So the criterion in part 4(b) of the
  bh-invent-13 node (`f − f(1) = b_γ` for a descending ray `γ`) is sufficient for (C2). Its
  "equivalently" should be read as the direction (HL) ⇒ (C2).

## Lesson for general BH

On hyperbolic geometry, finite type costs nothing up to one question. Local distance patterns already
force:
- a unique sink, hence an isolated seed;
- a unique centre with fellow-travelling descents for every other point, making each of them a
  Coornaert–Papadopoulos horofunction.

What is left is a statement purely about the horofunction boundary: whether every integral CP
horofunction is a limit of distance functions. It lives in a bounded tube around one ray. So SFT
compactifications of hyperbolic, including Kazhdan hyperbolic, groups hinge on one tube lemma, not on the
input. The hard inputs `H_Γ` are not hyperbolic, so this remains calibration for (★𝒞).
