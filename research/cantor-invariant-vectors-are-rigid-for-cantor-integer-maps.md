---
rg: 2
id: cantor-invariant-vectors-are-rigid-for-cantor-integer-maps
kind: claim
title: "In C(C,Z) ⋊ V, a V-invariant unit vector ξ lies within ‖π(1_[0])ξ − ξ‖/√2 of the C(C,Z)-invariant vectors; hence every V-invariant cnd function N on C(C,Z) satisfies sup_n N(n·1_C) ≤ 2N(1_[0]), and no exactly invariant (compound Poisson) law witnesses central growth"
distinct_from:
  cantor-integer-maps-central-direction-has-relative-t: that is the open relative-(T) assertion for the centre, about almost invariant vectors; this proves the exact-invariance case with a sharp constant and kills the jump-type e^{-tN} witnesses with N V-invariant, the canonical survivor listed there.
  cantor-integer-maps-pair-lacks-relative-property-t: that builds almost-V-invariant random-cone witnesses with no A-invariant vector; this shows no such witness can be exactly V-invariant, so the obstruction there is carried entirely by the V-defect.
  cantor-central-gaussian-scale-mixture-witnesses-die: that kills Gaussian laws by quadratic inclusion-exclusion; this kills every exactly invariant law, Gaussian or jump-type, by de Finetti and idempotent measures, with no moment assumption.
  cantor-integer-relative-t-witnesses-avoid-measure-characters: that screens almost invariant sequences off special character sets and notes Haar measure survives every screen; this classifies all exactly invariant laws (Haar measure included) and shows they are rigid near 0.
  cantor-integer-maps-central-growth-criterion: that reduces central growth to almost invariant vectors without 1_C-invariant vectors; this shows the almost invariant vectors in that criterion can never be taken exactly V-invariant.
---

**ESTABLISHED** by `cantor-invariant-vectors-are-rigid-for-cantor-integer-maps-proof` (unreviewed).

**Setting.** `C = {0,1}^N`, `A = C(C,Z)`, `G = A ⋊ V`, `z = 1_C` (central). `Â` is the compact
dual of `A`: the `T`-valued finitely additive set functions on the clopen algebra. `Q` is the set of
proper nonempty clopen sets. For a unitary representation `π` of `G` and a unit vector `ξ`, write
`Φ_ξ(f) = ⟨π(f)ξ, ξ⟩` and `μ_ξ` for the `A`-spectral law of `ξ` on `Â`.

**Theorem.** Let `μ` be a `V`-invariant Borel probability measure on `Â`, with Fourier transform
`Φ(f) = ∫χ(f) dμ`. Then there is a Borel map `χ ↦ H(χ)` into the closed subgroups of `T` with:
1. `μ`-a.s., `χ(U) ∈ H(χ)` for every `U ∈ Q`;
2. along every sequence of pairwise disjoint sets in `Q` whose finite unions are never `C`, the values
   `χ(U_i)` are conditionally i.i.d. with law `Haar(H(χ))` given `H(χ)`;
3. `Φ(1_U) = μ{H = {1}} = μ{χ = 0}` for every `U ∈ Q`. In particular `Φ(1_U)` is real, and
   `μ{χ(1_C) ≠ 1} ≤ μ{χ ≠ 0} = 1 − Φ(1_U)`.

**Corollaries.**
- (Rigid invariant vectors.) If `π(v)ξ = ξ` for all `v ∈ V`, then `‖ξ − P_Aξ‖² = ‖π(1_U)ξ − ξ‖²/2`
  for every `U ∈ Q`, where `P_A` projects onto the `A`-invariant vectors. The same bound holds with
  `P_A` replaced by the projection onto `π(z)`-invariant vectors.
- (Invariant cnd functions.) If `N` is a `V`-invariant cnd function on `A`, then
  `sup_n N(n·1_C) ≤ 2N(1_{[0]})`. The cnd functions `ψ(f,v) = N(f)` on `G` are therefore all bounded
  on `<z>`.
- (Class-kill.) No witness against relative (T) of `(G, <z>)`, and none against relative (T) of
  `(G, A)`, can be exactly `V`-invariant. This covers compound Poisson laws `e^{−tN}` with `V`-invariant
  Lévy measure, Haar measures of closed invariant subgroups and their cosets, and all mixtures.

**Where every member dies.** At idempotence. Merging two pieces of a disjoint sequence does not change
its tail, so the directing measure `ρ` satisfies `ρ * ρ = ρ` and is `Haar(H)`. A nontrivial `H` costs
mean `0` on every piece; the trivial `H` forces `χ = 0`.

**What it leaves.** Every witness needs a `V`-defect that cannot be removed. The exact argument
works equally for `A` and for `z`, and for `A` its almost-invariant analogue is false
(`cantor-integer-maps-pair-lacks-relative-property-t`). So every approximate-exchangeability proof of
central relative (T) dies where it would show that the directing measure is near `δ_1`. This covers
finite de Finetti and stability of idempotents. Such a proof must use an input that separates
`z = χ([0])χ([1])` from a general element of `A`. See the proof, §5.

**Relation to a parallel result.** Worker `swarm-0917-w8-w8-nv-pull` proved, on the same day and in
another worktree, the node `cantor-central-v-elliptic-witnesses-die`, which has not landed. It shows
by Cesàro averaging that `φ(k·1_U) ≥ φ(1_U) ≥ 0`, and hence that cnd functions bounded on `V` are
bounded on `z`. This node overlaps it on the invariant-cnd corollary. What this node adds:
- the classification of the directing measure as `Haar(H)`;
- the identity `Φ(1_U) = μ{χ = 0}`, i.e. exact rigidity for the whole pair `(G, A)` on `V`-fixed
  vectors;
- the constant `2`;
- the §5 obstruction to any quantitative upgrade.
If both land, they should be cross-linked by `distinct_from`.
