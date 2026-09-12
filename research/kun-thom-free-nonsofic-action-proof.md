---
rg: 2
id: kun-thom-free-nonsofic-action-proof
kind: route
title: Multiply the nonsofic generalized Bernoulli action by a free Bernoulli shift and restrict the embedding to the first factor
target: kun-thom-free-nonsofic-action
requires:
  - kun-thom-nonsofic-wreath
artifacts:
  - research/artifacts/free-nonsofic-action-sources-verified-2026-09-11.md
---

# Derivation from Corollary D

This is Kun--Thom's own proof of Corollary 3.2 (v3, p. 7), written out so the
graph can check its one external input. The only theorem consumed is Corollary D
(`kun-thom-nonsofic-wreath`): under its hypotheses the generalized Bernoulli
action `G ↷ (K,κ)^(G/Γ)` is not sofic for every nontrivial standard `(K,κ)`.

**Step 0, infinite index.** If `[G:Γ] < ∞`, every `t ∈ P_Γ` gives
`tΓt^(-1) <= Γ` with the same finite index, so `tΓt^(-1) = Γ`. The compression
semigroup is then contained in the normalizer, and since `P_Γ` generates `G`,
`Γ` would be normal. So `[G:Γ] = ∞`.

**Step 1, the action.** Let `Y = ({0,1},ν)^(G/Γ)` and `B = ({0,1},ν)^G` with `ν`
fair, and `X = Y × B` with the diagonal action. `G` acts transitively on the
infinite set `G/Γ`, so `Y` is ergodic (all orbits infinite). `B` is mixing and
essentially free because `G` is infinite. So `X` is essentially free (a fixed
point set of `g ≠ 1` in `X` lies in `Y × Fix_B(g)`, which is null) and ergodic
(product of a weakly mixing generalized Bernoulli action with an ergodic one).

**Step 2, soficity passes to factors.** If `L^∞(Z) <= L^∞(X)` is a
`G`-invariant von Neumann subalgebra, the von Neumann algebra generated inside
`L^∞(X) ⋊ G` by `L^∞(Z)` and the `u_g` is trace-preservingly isomorphic to
`L^∞(Z) ⋊ G`: both are the GNS completion of the algebraic crossed product for
the trace `τ(a u_g) = τ(a) δ_(g,1)`. Restricting a sofic embedding of
`L^∞(X) ⋊ G` still sends the base into the diagonal and each `u_g` to a
permutation. So every factor of a sofic action is sofic.

**Step 3, contradiction.** `Y` is a factor of `X` (projection to the first
coordinate). If `X` were sofic, `Y` would be sofic by Step 2, contradicting
Corollary D. So `X` is a free ergodic nonsofic action.

**Step 4, strong ergodicity.** Every ergodic p.m.p. action of a Kazhdan group is
strongly ergodic (Connes--Weiss); Kun--Thom cite it as their reference [5].

**Step 5, the orbit relation.** `X` is free, so Păunescu Proposition 1.15
(transcribed in the artifact) turns nonsoficity of the action into nonsoficity of
its orbit equivalence relation. For the Theorem E pair, `G` is residually finite.
