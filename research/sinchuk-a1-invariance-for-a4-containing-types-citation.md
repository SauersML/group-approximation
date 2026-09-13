---
rg: 2
id: sinchuk-a1-invariance-for-a4-containing-types-citation
kind: route
title: Sinchuk Theorem 1.1, read from arXiv:2412.06944v1
target: sinchuk-a1-invariance-for-a4-containing-types
requires: []
---

**Literature import.** Sergey Sinchuk, *On the A^1-invariance of K_2 of
Chevalley groups of simply-laced type*, arXiv:2412.06944v1 (submitted
9 Dec 2024, the only version on arXiv). Journal reference on the abs page:
European Journal of Mathematics 11, 14 (2025). The HTML was fetched on MSI on
2026-09-12, and the statement below was extracted from it with the math markup
flattened.

**Theorem 1.1** (the K_2-analogue of the Lindel--Popescu theorem). "Let k be
an arbitrary field and R be a regular ring containing k. Let Φ be an
irreducible simply-laced root system containing A_4 but not of type E_8. Then
for any lattice Λ as above and G = G_Λ(Φ, −) one has
K_2^G(R[t]) ≅ K_2^G(R)."

**Corollary 1.2** (same source): for `k`-smooth `R`,
"π_1^{A^1}(G)(R) := Hom_{H_•(k)}(S^1 ∧ Spec(R)_+, G) = KV_2^G(R) = K_2^G(R)".

**Match with the target.** The target is Theorem 1.1:
- any field `k`;
- a regular ring `A ⊇ k`;
- `Φ` irreducible, simply laced, containing `A_4`, not `E_8`;
- any lattice.

The paper writes `≅`. The target reads it as: the canonical polynomial
extension map `K_2^G(A) → K_2^G(A[t])` is an isomorphism. Reason for that
reading: `A → A[t] → A`, with `t ↦ 0`, makes the canonical map split injective.
The theorem is framed as A^1-invariance, and Corollary 1.2 identifies `K_2^G`
with an A^1-homotopy invariant functor, where invariance means exactly this.
The target's remarks follow:
- type `A_(r-1)` contains `A_4` iff `r ≥ 5`;
- iteration adjoins finitely many variables;
- the statement is unstable.

**Not verified here.** The journal version was not consulted. The target node
says "version dated 2026-03-22", but the arXiv abs page lists only v1
(9 Dec 2024).
