---
rg: 2
id: thompson-f-following-models-separate-iff-mean-charges-commutator
kind: claim
title: Permutation models following an F-set can separate the commutator exactly when an invariant mean on the F-set charges its moved points
distinct_from:
  thompson-f-spatial-permutation-models-almost-commute: that bounds the commutator for F-sets over the interval under a hypothesis on c; this characterizes separation on every F-set through invariant means, and shows all nontrivial elements of F' move the same mean-mass.
  thompson-f-sofic-iff-relator-system-unstable: that makes soficity of F equivalent to separating almost-solutions of the relators; this decides when such almost-solutions can follow a genuine action of F.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that builds Følner sets in some Schreier graphs of F; this asks when an invariant mean charges the points moved by the commutator.
artifacts:
  - research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md
---

**ESTABLISHED.** **Setting.**
- `x_0, x_1` are the standard generators of `F`, composed right to left, `c = x_0 x_1 x_0^-1 x_1^-1`,
  and `F'` is the commutator subgroup.
- `Ω` is any `F`-set and `Moved(g) = {ω : gω ≠ ω}`.
- A mean on `Ω` is a positive normalized linear functional on `ℓ∞(Ω)`. It is invariant if
  `m(1_(gE)) = m(1_E)` for all `g ∈ F` and `E ⊆ Ω`.
- A *labelled model* on `Ω` is a finite set `S`, an injection `π : S → Ω` and `A, B ∈ Sym(S)`. Its
  error `δ` is the larger of two fractions: the `s` with `π(As) ≠ x_0 π(s)`, and the `s` with
  `π(Bs) ≠ x_1 π(s)`.

**Statement.**
1. **Means from models.** If labelled models on `Ω` have `δ_n → 0` and `d(A_nB_n, B_nA_n) ≥ ε`,
   then some invariant mean on `Ω` has `m(Moved(c)) ≥ ε`.
2. **Models from means.** Suppose some invariant mean on `Ω` has `m(Moved(c)) = η > 0`. Then for every
   `δ > 0` there are a finite `S ⊆ Ω` and a model labelled by inclusion with:
   - error at most `δ`;
   - both relator defects at most `14δ`;
   - `d(AB, BA) > η/2 - 4δ`.

   So `F` is sofic.
3. **Uniform mass.** For every invariant mean on every `F`-set, `m(Moved(g)) = m(Moved(c))` for all
   `g ∈ F' \ {e}`.
4. **Slabs are null.** For every invariant mean and every equivariant `p : Ω → [0,1]`,
   `m(p^-1[y,z]) = 0` whenever `0 < y ≤ z < 1`.

**Corollaries.** Write `t = m(Moved(c))`.
- **Kernel.** `t = 0` if the action has a nontrivial kernel.
- **Confined moved sets.** `t = 0` if some `g ∈ F' \ {e}` has
  `Moved(g) ⊆ p_1^-1[y,z] ∪ ... ∪ p_k^-1[y,z]` for equivariant maps `p_i : Ω → [0,1]` and
  `0 < y ≤ z < 1`.
  - This covers points, finite configurations, intervals, germs at points and the Cantor set, for any
    compactly supported `g`, with no hypothesis on `c`.
  - Together with item 1 it recovers the qualitative form of
    `thompson-f-spatial-permutation-models-almost-commute`.
- **Witnesses.** A witness for `thompson-f-is-sofic` that follows some `F`-set exists exactly when
  some `F`-set carries an invariant mean charging `Moved(c)`. On such an `F`-set:
  - every nontrivial element of `F'` moves mean-mass `t`;
  - no equivariant map to the interval confines any of their moved sets to a slab.

**Scope.** Elementary. The Day and Namioka steps are the standard ones, written out in the route, and
no novelty is claimed. It decides nothing about `thompson-f-is-sofic`; it turns the construction
problem for following models into a problem about invariant means.
`thompson-f-interval-stabilizer-cosets-separate-only-if-amenable` settles natural coset spaces that
`thompson-f-spatial-permutation-models-almost-commute` does not cover.

Proof route: `thompson-f-following-models-mean-charges-commutator-proof`.
