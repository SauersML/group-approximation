---
rg: 2
id: li-shen-amalgamated-rfd-criterion
kind: claim
title: "Li–Shen: a unital full amalgamated free product of separable C*-algebras over a finite-dimensional algebra is RFD iff both factors embed unitally in one product of matrix algebras compatibly on the amalgam"
---

**ESTABLISHED (import).** Let `A`, `B` be separable unital C*-algebras, `D` a finite-dimensional C*-algebra, and `ψ_A: D → A`, `ψ_B: D → B` unital embeddings. Then `A *_D B` is residually finite-dimensional iff there are a sequence of integers `(k_n)` and unital embeddings `q_1: A → ∏_n M_{k_n}(C)`, `q_2: B → ∏_n M_{k_n}(C)` with `q_1∘ψ_A = q_2∘ψ_B`.

Source: Q. Li and J. Shen, "A note on unital full amalgamated free products of RFD C*-algebras", Illinois J. Math. 56 (2012), no. 2, 647–659, Theorem 2 (p. 657).
- The product is the full direct product ∏ (not an ultraproduct), and the compatibility is exact equality on `D`.
- The same paper, Example 1 (p. 650): `M_2(C) *_{C⊕C} M_3(C)`, with `1⊕0` of rank 1 in both, is not MF, so it is not RFD. This is the model test showing a rank-ratio condition is necessary.

Route: `li-shen-amalgamated-rfd-criterion-citation`.

## Review
- **sk-verify-18 PASS at source (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part2.md`):**
  - Theorem 2 (p. 657), Lemma 6 (p. 657), the proof reduction (p. 658), Example 1 and Remark 2 (p. 650) read verbatim in the journal PDF, doi 10.1215/ijm/1385129969 (Crossref-confirmed).
  - The same criterion appears as Theorem 4.1 of the arXiv preprint 1006.2447.
