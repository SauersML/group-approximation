---
rg: 2
id: subshift-group-unitary-embeddings-are-corner-subfactors-proof
kind: route
title: Character rigidity splits every finite representation of G_X into trivial plus regular, and the corner count is Ozawa's
target: subshift-group-unitary-embeddings-are-corner-subfactors
requires:
  - subshift-elementary-groups-are-character-rigid
  - simple-kazhdan-lef-group-from-minimal-subshift
  - separable-factors-hold-countably-many-subshift-groups
artifacts:
  - research/artifacts/sk-vn-rigidity-2026-09-14.md
---

Notation: `G = G_X`, `(M,τ)` with `τ` a faithful normal tracial state, and `ι: G → U(M)` a homomorphism.

**Step 1: the trace of `ι` is a character.**
- `φ = τ∘ι` is positive definite, normalized, and constant on conjugacy classes, since `τ` is tracial.
- By `subshift-elementary-groups-are-character-rigid`, `φ = c·1 + (1−c)δ_e` with `c ∈ [0,1]`.
- If `c = 1`, then `‖ι(g) − 1‖_2^2 = 2 − 2Re τ(ι(g)) = 0` and `ι` is trivial. So a nontrivial `ι` has `c < 1`.

**Step 2: the GNS decomposition.**
- Let `N = ι(G)''` and `H = L^2(N,τ)`, the closure of `Nι̂`. The representation `g ↦ ι(g)` on `H` is the GNS representation of `φ`.
- The GNS representation of `c·1 + (1−c)δ_e` is the direct sum of the trivial representation `π_0` (vector of norm² `c`) and
  the left regular representation `λ` (vector `(1−c)^{1/2}δ_e`). `G` is infinite, so `λ` has no invariant vectors and
  `π_0`, `λ` are disjoint.
- For disjoint subrepresentations the projection onto each summand lies in the centre of the generated von Neumann algebra.
  So there is a central projection `z ∈ Z(N)` with `ι(g)(1−z) = 1−z` and `N z ≅ λ(G)'' = L(G)`, the isomorphism
  `ι(g)z ↦ λ_g` being normal and trace-scaled by `τ(z) = 1−c`.
- `z ∈ N ⊆ M` and `Nz ⊆ zMz` is unital, which gives (1).
- `c = τ(ι(e_12(e_P)))`: `e_12(e_P) ≠ e` for nonempty clopen `P`.

**Step 3: (2).**
- (⇒) is (1).
- (⇐) Given a unital `L(G) ≅ Q ⊆ zMz`, put `ι(g) = (1−z) + v_g`, where `v_g` is the image of `λ_g`. This is a homomorphism
  into `U(M)`, injective because `λ` is.

**Step 4: (3).**
- A corner embedding gives, by Step 3, a subgroup of `U(M)` isomorphic to `G_X`.
- By `separable-factors-hold-countably-many-subshift-groups` (item 1, reviewed sk-verify-10), only countably many `X ⊆ A^Z` qualify.

**Model tests.**
- `M = C`: the only homomorphism is trivial (`G_X` is perfect and simple), with `c = 1`, consistent.
- `M = L(G_X)` with `ι = λ`: `c = 0`, `z = 1`.
- `M = L(G_X) ⊕ C` with `ι = λ ⊕ 1`: `c = 1/2` for the normalized trace, and `z` is the first summand.
- For the derived topological full group `[[T]]′`, Dudko–Medynets characters `∏μ_i(Fix γ)` give non-regular factor
  representations, so the analogue of (1) fails there. This is consistent: that group is not character rigid.
