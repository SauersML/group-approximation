---
rg: 2
id: ray-germ-one-point-groups-are-v-point-stabilizers
kind: claim
title: A one-point germ extension of V whose germs are independent translations of finitely many rays of blocks is a stabilizer of finitely many rational points in V, hence of type F_∞, unlike the corresponding Houghton group
distinct_from:
  shell-one-point-groups-are-ascending-hnn-over-window-lifts: that proves a sufficient condition for finiteness of the shell's one-point group; this computes the one-point group exactly when the germ group is virtually Z^k acting by ray translations.
  bhm-singfix-condition-forces-fp-germ-groups: that forces finite presentation of the germ group from the one-point group; this is a family where the germ group's finiteness, F_∞ for Z^k, passes back up to the one-point group.
---

**ESTABLISHED** (lane proof, bh-free-08, 2026-09-18; elementary; not reviewed; no novelty claimed). It is a calibration for the open converse "a germ group of type `F_n` gives a one-point group of type `F_n`".

## Setting

- **Blocks.** `C = {0,1}^N`, `p = 0^∞`, and the blocks `B_n = [0^n1]`, so that `C ∖ {p} = ⊔_n B_n`.
- **Rays and their shifts.** Partition `N` into `k ≥ 1` infinite sets `R_1, …, R_k`, each listed in increasing order. Let `σ_i` be the near permutation of `N` that moves the `j`-th element of `R_i` to the `(j+1)`-th and fixes the other rays. Let `Γ` be a group of near permutations of `N` containing `Z^k = ⟨σ_1, …, σ_k⟩` with finite index, whose elements permute the rays, meaning they map each ray into some ray up to finitely many points.
- **The one-point group.** `A(Γ)` is the group of homeomorphisms `h` of `C` with `h(p) = p` that are locally `V` on `C ∖ {p}` and whose germ at `p` acts on blocks by a rigid block permutation (`B_n → B_(β(n))` identically for all large `n`) with `[β] ∈ Γ`.

## Statement

1. `A(Z^k) ≅ Fix_V(q_1, …, q_k)`, the pointwise stabilizer in `V` of `k` distinct rational points.
2. `A(Γ)` contains `A(Z^k)` with finite index, and is isomorphic to a subgroup of the setwise stabilizer `Stab_V({q_1, …, q_k})`.
3. Hence `A(Γ)` has type `F_∞` (BHM arXiv:2407.03149v1, Appendix A, Theorem `thm:Stabilizers`).

## Proof

**Blowing up `p`.** Choose disjoint cones `[w_1], …, [w_k]` partitioning `C`, and put `q_i = w_i 0^∞`. Define `Φ: C ∖ {p} → C ∖ {q_1, …, q_k}` by sending the `j`-th block of `R_i` onto `[w_i 0^j 1]`, by the prefix replacement `0^n 1 z ↦ w_i 0^j 1 z`. `Φ` is a bijection of the block partitions, and every block map is a prefix replacement. So `Φ` carries homeomorphisms that are locally `V` on `C ∖ {p}` to homeomorphisms that are locally `V` on `C ∖ {q_i}`. It carries the rigid germ `σ_i` near the tail of `R_i` to `w_i 0^j 1 z ↦ w_i 0^(j+1) 1 z`, the `V`-germ `τ_(q_i)` at `q_i`.

**1.** Let `h ∈ A(Z^k)`. Its germ is `∏ σ_i^(a_i)`, so for large blocks `h` preserves each ray and translates it by `a_i`. Then `h' = Φ h Φ^{-1}`, extended by `h'(q_i) = q_i`, is continuous at each `q_i`: a neighbourhood `{q_i} ∪ ⋃_(j ≥ J) [w_i 0^j 1]` goes to a neighbourhood of the same shape. It is locally `V` off `{q_i}`, and near `q_i` it equals `τ_(q_i)^(a_i)`, which is locally `V`. Since `V` is full, `h' ∈ V`, and `h'` fixes every `q_i`.

Conversely, `v ∈ Fix_V(q_1, …, q_k)` has germ `τ_(q_i)^(a_i)` at each `q_i`, since `(V)_q = ⟨τ_q⟩` at rational points. So `Φ^{-1} v Φ`, extended by fixing `p`, lies in `A(Z^k)`, with germ `∏ σ_i^(a_i)`. The two maps are mutually inverse homomorphisms.

**2.** `A(Z^k) = π^{-1}(Z^k)` under the germ map `π: A(Γ) → Γ`, so its index is `[π(A(Γ)) : Z^k] ≤ [Γ : Z^k] < ∞`. An element `h` of `A(Γ)` maps tails of rays to tails of rays by some permutation of `{1, …, k}` and translates along them. Conjugating by `Φ` gives a homeomorphism that permutes the `q_i` and is locally `V`, so it lies in `Stab_V({q_i})`. The rest of the argument is as in 1.

**3.** `Fix_V(M)` is `F_∞` for finite sets `M` of rational points, and `F_∞` passes to finite-index overgroups. ∎

## Contrast (the reason for this node)

- **Houghton.** Replace "locally `V`" by "finitary permutation of blocks", so that every element is a genuine permutation of the blocks, and germs are confined to the index-zero sublattice `Z^(k-1)` of `Z^k`. The result is Houghton's group `H_k`. Brown proved `H_k` has type `F_(k-1)` but not `F_k`, although its germ group `Z^(k-1)` is `F_∞`.
- **`V` coefficients.** With `V` coefficients the finiteness of the germ group passes up unchanged. This is the mechanism that makes the one-point group of a virtually cyclic shell `F_∞`.
- **Evidence only.** It supports, but does not prove, the converse needed by the shell route: that the one-point group `A_1` inherits the finiteness of the germ group `Q_ν`. The germ groups here preserve a finite ray decomposition. Shell germ groups of inputs that are not virtually cyclic do not.
