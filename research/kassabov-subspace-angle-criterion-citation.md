---
rg: 2
id: kassabov-subspace-angle-criterion-citation
kind: route
title: Import Kassabov's positive definite angle criterion (Theorem 1.2 with Observation 2.1)
target: kassabov-subspace-angle-criterion
requires: []
---

Citation import, not a reproof.

M. Kassabov, *Subspace arrangements and property T*, arXiv:0911.1983v2 (1 Dec 2009). The PDF was
downloaded from arXiv on MSI, and pages 1–8 were read as rendered page images on 2026-09-13
(lane ex2-triangle-persistence). Verbatim:

- **Theorem 1.2.** "Let V_i be n closed subspaces in a Hilbert space H. If for any pair of indexes
  1 ≤ i, j ≤ n we have cos ∢(V_i, V_j) ≤ ε_ij and the symmetric matrix A = (1 on the diagonal,
  −ε_ij off the diagonal) is positive definite. Then, the angle ∢(V_1, V_2, …, V_n) ≥ φ > 0, where the
  constant φ depends only on the matrix A." The matrix is displayed in the source; it is paraphrased
  inside the parentheses here.
- **Observation 2.1.** "Let G be a group and let G_i be a collection of n subgroups in G such that
  G = ⟨G_1, …, G_n⟩. Then the Kazhdan constant κ(G, ∪G_i) is strictly positive if and only if there
  exists α > 0 such that ∢(H^{G_1}, H^{G_2}, …, H^{G_n}) > α for any unitary representation H of G. In
  particular, if all G_i are finite subgroups and there exists lower bound for then angle, then G has
  Kazhdan property T."
- **Definition 3.2.** "cos ∢(V_1, V_2) = sup{ |⟨v_1, v_2⟩| : ‖v_i‖ = 1, v_i ∈ V_i, v_i ⊥ (V_1 ∩ V_2) }",
  stated when neither space contains the other. Remark 3.4 says the angle "should be equal" to π/2 when
  `V_2 ⊂ V_1`.
- **Context, p. 3.** "Ershov and Jaikin [13, Theorem 5.9] also proved an analog of Theorem 1.2 in the case
  n = 3."

Applying Theorem 1.2 with `α = φ/2` inside Observation 2.1 gives the claim.

**Verification boundary.**
- The proof of Theorem 1.2 (Sections 4–5) was not re-read.
- The published version (Groups Geom. Dyn.) was not compared with the arXiv text.

This route asserts only that the source says what the claim records.
