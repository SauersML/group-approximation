---
rg: 2
id: frobenius-bicommutants-make-subshift-el3-isos-standard
kind: claim
title: Given the index kernel theorem, the double centralizer of the image of a constant Frobenius group is one natural block, which forces orthogonality of supports, no fixed vectors, constant orientation, and so standardness of every isomorphism G_X → G_Y
distinct_from:
  singer-identities-make-subshift-el3-isos-standard: that assumes the Singer identities and (O′); this proves them from bicommutants and the index kernel theorem
  frobenius-support-idempotents-give-boolean-realization: that assumes (O) and (O′); this proves both
  subshift-el3-isomorphisms-are-standard-over-f2: that is the open question; this answers it modulo the unreviewed index kernel theorem
artifacts:
  - research/artifacts/sk-orthogonality-o-2026-09-14-part2.md
  - research/artifacts/sk-orthogonality-o-2026-09-14-part1.md
---

Let `X, Y` be infinite minimal subshifts, `G_X = EL_3(LC(X,F_2)⋊Z)`, `α: G_X → G_Y` an isomorphism, `Q = GL_3(F_2)`,
`F21 ≤ Q` the Frobenius group of order 21, `K_V = α(F21_V)` and `S_V = I + Σ_{k∈K_V} k`. Assume the index kernel
theorem `subshift-gl3-index-kernel-is-elementary-group` for `X` and `Y`. Then:

1. **(Lemma X)** `C_{G_X}C_{G_X}(F21_V) = Q_V`.
2. **(Theorem C)** On `R_Y³`, `K_V` has exactly one of the types `3`, `3*` and no type `2`. `α(Q_V)` is trivial on
   `Fix(K_V)` and acts as `ψ_V(q) ⊗ id` on the other block.
3. `S_VS_W = 0` for disjoint `V, W`, and `S_X = I`.
4. The orientation `t_V` does not depend on `V`.
5. **(Theorem D)** `α`, or `α∘γ_X` with `γ_X` the graph automorphism, satisfies the Singer identities. So `α` is
   standard, and `G_X ≅ G_Y` implies that `X` and `Y` are strongly orbit equivalent.

Status: proved in `frobenius-bicommutants-make-subshift-el3-isos-standard-proof`, unreviewed. It is conditional on
the unreviewed index kernel theorem and on the flagged first-return corner isomorphism.

Model tests:
- the identity, `inn(diag(u,1,1))` and `γ_X` all fit the conclusions;
- Petechuk's non-standard automorphism over a product ring breaks Lemma X, because the ring is not simple.

## Review
- **sk-verify-25b PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-25b-2026-09-14.md` §§3–5):** adversarial re-derivation of Lemma Z, Lemma X, Theorem C, Lemma S3 and Corollaries O, O′, T, and of Theorem D.
  - **Combined PASS:** every isomorphism `α: G_X → G_Y` equals `inn(k)∘Θ∘γ_X^ε` for a ring isomorphism `Θ: M_3(R_X) → M_3(R_Y)`, `k ∈ GL_3(R_Y)` and `ε ∈ {0,1}`. So `G_X ≅ G_Y` implies strong orbit equivalence.
  - **No counterexample:**
    - `inn(diag(u^k,1,1))`: outer, but standard;
    - `γ_X` and ring anti-automorphisms;
    - flip-conjugacy and SOE ring isomorphisms;
    - central or index twists (G_X perfect and centreless);
    - locally mixed orientation (Corollary T; `R_Y` simple).
  - **Computed on MSI:**
    - Sym ⊆ 3⊗3 has no invariant complement to Λ²;
    - Stab(e_1) fixes no nonzero vector of Λ²;
    - finite model R = M_4(F_2), |V| = 2: dim C(F21_V) = 40, dim CC = 10 with 168 units;
    - a mixed 3⊕3* image has 168² units in its double commutant.
  - **Fixes:**
    - C1: the index kernel theorem is reviewed (sk-verify-18 PASS); update the status line.
    - C2: drop the first-return corner isomorphism import. Lemma X needs only that `R_V = e_VR_Xe_V` is simple with centre `F_2e_V`, and this follows because a corner of the simple ring `R_X` is simple and, `e_V` being full, `Z(e_VR_Xe_V) = e_VZ(R_X)`. With Fix A2 on `singer-identities-make-subshift-el3-isos-standard`, Theorem D uses only reviewed imports and Matui Lemma 2.5, which was read at source.
    - C3: in Theorem C, `g_t(a) ∈ F_2I + span_{F_2}K_V`, since the t-component of `F_2[F21]` is `M_3(F_2)` (`F_4` for t = 2). So it commutes with `C_{G_Y}(K_V)`.
    - C4: scope. This answers the "at least strongly orbit equivalent" alternative of the note's question; flip conjugacy stays open. The route's `requires` entry `diagonal-recognition-makes-subshift-el3-isos-standard` is unused.
