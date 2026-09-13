---
rg: 2
id: thompson-f-spatial-permutation-models-almost-commute
kind: claim
title: Permutation models that follow Thompson's F acting on the interval almost commute
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that builds almost-invariant finite sets in orbits of F; this shows that the permutation pairs they give almost commute, and so does every pair that follows an action of F over the interval.
  thompson-f-relator-system-stable-in-permutations: that asks for the commutator bound for every almost-solution; this proves it only for almost-solutions that follow F's action on points, intervals, finite configurations or the Cantor set.
  thompson-v-cantor-orbits-have-no-folner-sets: that says V's Cantor orbits have no Følner sets; orbits of F do have them, and this bounds the commutator of the models they give.
artifacts:
  - research/artifacts/thompson-f-spatial-permutation-models-2026-09-13.md
---

**ESTABLISHED.** **Setting.**
- `x_0, x_1` are the standard piecewise linear generators of `F` on `[0,1]`, composed right to left,
  and `c = x_0 x_1 x_0^-1 x_1^-1`.
- `Ω` is an `F`-set with an equivariant map `p = (p_1, ..., p_k) : Ω → [0,1]^k` such that `c` fixes
  every `ω` with no `p_i(ω)` in `[1/4, 3/4]`.
- `S` is finite, `π : S → Ω` is injective, and `A, B ∈ Sym(S)`.
- `π(As) = x_0 π(s)` fails for at most `δ|S|` points `s`, and so does `π(Bs) = x_1 π(s)`.

**Statement.** In normalized Hamming distance,

`d(AB, BA) ≤ 4δ + k sqrt(6δ)`,

and `d(w(A,B), 1) ≤ |w| δ` for every word `w` with `w(x_0, x_1) = 1`, including both relators of
`F`.

**Instances.**
- Points of `[0,1]` (`k = 1`).
- Closed intervals and dyadic cones, through their endpoints (`k = 2`).
- `k`-point configurations.
- The Cantor set, through binary value (`k = 1`).

So truncated dyadic-tree models with any boundary or reservoir repair, and the `x_0`-ray windows of
`thompson-f-end-rigid-schreier-graphs-are-amenable`, all have separation at most `4δ + 2 sqrt(6δ)`.

**Consequence.** Take a family as in `thompson-f-sofic-iff-relator-system-unstable`, with
`d(A_nB_n, B_nA_n) ≥ ε`. Under every such labelling it disagrees with `F`'s action on at least a
`min(ε/8, ε²/(24k²))` fraction of points. Spatial almost-solutions exist, since `δ → 0` forces relator
defect `→ 0`, but none of them separates the commutator. The artifact has exact profiles:
- truncations keep `δ` near `1/4` and relator defect above `0.53`;
- `x_0`-rays drive everything to 0 together;
- perturbed commuting pairs pay about twice their separation in defect.

**Scope.** Elementary. It excludes a construction route and decides nothing about
`thompson-f-is-sofic`.

Proof route: `thompson-f-spatial-permutation-models-almost-commute-proof`.
