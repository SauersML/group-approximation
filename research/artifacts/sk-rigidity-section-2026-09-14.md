# sk-rigidity-section: the rigidity theorem for G_X, as a note section (Option N) or a separate paper (Option P) (2026-09-14)

Lane sk-rigidity-section. This first landing is the plan and the dependency measurement. The candidate section, its compile and the final recommendation follow in a later landing of this file.

## 0. Statement (passed twice)
For infinite minimal subshifts X, Y and any isomorphism α: G_X → G_Y there are k ∈ GL_3(R_Y), a ring isomorphism φ: R_X → R_Y and ε ∈ {0,1} with α∘γ_X^ε = inn(k)∘M_3(φ)|_{G_X}. So G_X ≅ G_Y ⇔ R_X ≅ R_Y, and both imply that X and Y are strongly orbit equivalent.
- Reviews: sk-verify-25a (248bd5cc91; W1–W5) and sk-verify-25b (5affb84500; A1–A3, C1–C4). No gap.
- Open: flip conjugacy, and L(G_X) ≅ L(G_Y) ⇒ G_X ≅ G_Y.

## 1. Every input of a complete proof
The note proves everything it states, so Option N must reprove or cite every input.

| Input | Reviewed node | Cost if printed |
|---|---|---|
| Z(R) = F_2; corner centre and maximal commutativity of LC(V) | rigid-supports C1, bicommutant route (sk-verify-3, -5) | ~0.15 p |
| C_G(G_U) = G_{X∖U}; span(G_U − I) = M_3(e_URe_U) | rigid-supports C1–C2 (sk-verify-3) | ~0.1 p |
| CC(A_ij(R)) = A_ij(R) | bicommutant closedness item 2 (sk-verify-5) | ~0.15 p |
| **Index kernel theorem**: ker(ind) = EL_3(R), so torsion ⊆ EL_3(R) ⊴ GL_3(R) | O1 (sk-verify-18 part6), resting on I1 (sk-verify-5) and Theorem D bounded generation (sk-verify-15, -16) | **~1.3 p** (Fredholm index, constancy, block Gauss reduction with Thompson 1961, end corrections, two-end inverse, tower assembly) |
| **Theorem DP**: idempotents of M_n(R) are similar to diagonal clopen idempotents | sk-algebraic-putnam part2 (sk-verify-16) | **~0.7 p** |
| K_0(R_X) ≅ C(X,Z)/(1−T_*), torsion-free | K_0 node (sk-verify-3) via Ara–Brustenga–Cortiñas Thm 3.6 + Lemma 7.2 | ~0.25 p (cited) |
| Order: [1_U] ≤ [1_V] ⇒ γU ⊆ V for some γ ∈ [[T]] | Matui arXiv:math/0404224 Lemma 2.5 (read at source by both verifiers) | cited |
| Ring iso ⇒ SOE | matrix ring ⇒ SOE (sk-verify-3) via GPS 1995 Thm 2.1 | ~0.2 p |
| Representation facts for F21 ≤ GL_3(2) | F1, F5, span F21 = M_3(F_2), C_Q(F21) = 1 (computed by both verifiers) | ~0.3 p |
| Lemma Z, Lemma X, Theorem C, Corollaries O, O′, orientation, coordinates, supports, roots, standardness | the two claim nodes (sk-verify-25a, -25b) | ~2.5 p |

**Estimated Option N cost: 5.5–6 pages, taking the note from 11 pp to about 17 pp.** Compile measurement to follow.

## 2. The shortest complete path, and what it drops
These are rearrangements of reviewed material. Each is flagged for a verifier.
- **S1 (drops F4, Ext¹ and projectivity of the Steinberg module).** Theorem A Step 2 is not needed inside the Theorem D chain. Theorem C at V = X with Corollary O′ (Fix(K_X) = 0) already gives M = t_X ⊗ P with α(Q_X) acting as ψ_X ⊗ id.
- **S2 (drops Lemma S3).** Corollary O can use F21-types instead of non-semisimplicity:
  - under the diagonal F21, (3⊗3) and (3*⊗3*) contain both 3 and 3* (F5), and 3⊗3* contains the type 2 (F1);
  - by Theorem C at V⊔W, M has only the types 1 and t_{V⊔W} under K_{V⊔W}.
  - So N = S_VS_WM = 0. UNREVIEWED as a justification; the facts used are reviewed.
- **S3 (drops Lemma 0 and the Singer identities).** Theorem A's hypotheses (Sing) are only used to reach (O), (O′) and the module type, which the Theorem D chain gives directly. Corollary T (constant orientation) is not used after the coordinates step either.
- **S4 (drops Proposition F).** Step 6 needs only α′(e_ij(e_V)) = I + b_VE_ij ∈ A_ij(R_Y), from 25b's A2 and Step 4. The Boolean embedding V ↦ b_V is not used.
- **S5 (drops Theorem P, measures and rank functions).** 25a's W3 gives φ directly. The positive cone of K_0(R_X) is the image of C(X,Z_{≥0}), directly from Theorem DP ([e] = Σ[1_{W_i}]), so GPS applies. UNREVIEWED as a justification; it replaces (R4)'s measure argument.

## 3. Recommendation (preliminary)
**P, a separate short paper,** unless the compile measurement is far below the estimate.
- The proof's toolkit (Fredholm index at a cut, tower compressions with Thompson's commutator theorem, algebraic Pimsner–Voiculescu, dimension groups, modular representations of GL_3(2)) is disjoint from the note's single mechanism.
- It would roughly double the note's proof content.
