---
rg: 2
id: loop-braid-pair-twist-push-complexity-fails-proof
kind: route
title: "Evaluate the antisymmetric clasp on the generators of both cabling stabilizers and on pair twists, then run an infinite descent from the vertex A_av[(a,b)]"
target: loop-braid-pair-twist-push-complexity-fails
requires:
  - pure-loop-braid-group-is-colimit-of-cabling-stabilizers
artifacts:
  - research/artifacts/zp-loop-braid-cx-antisymmetric-clasp-obstruction-2026-09-18.md
  - research/artifacts/zp-loop-braid-bfmwz-push-decomposition-2026-09-17.md
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
  - experiments/loop-braid-cx-obstruction-2026-09-17/antisym_clasp.py
---

The complete hand proof is in artifact §§2–3 (Lemmas 2.1, 2.2; Theorems 3.1, 3.2). It is unreviewed.
The inputs are:
- the cabling-subgroup generators and the strict fundamental domain Q, from
  `pure-loop-braid-group-is-colimit-of-cabling-stabilizers`;
- the Link Lemma `lk(b) = P_b · lk_Q(b)` (w8 artifact, Lemma 2.1), proved from the same inputs.

The proof has four steps.

1. **e is a homomorphism.** `P` acts trivially on `H_1(F_n)`, and the centralizer of `x_i` is `⟨x_i⟩`.
2. **Vanishing (Lemma 2.1).** Evaluate on the generators, where each `e`-vector is a sum of at most
   two unit vectors.
   - `θ_k`, `ζ_q` and their `(v,w)` analogues give `e_ka + e_kb` or `e_aq + e_bq`, and each such
     sum pairs coefficients `+1` and `−1`.
   - A pair twist gives `e_cd + e_dc`, which φ_ab kills because it is antisymmetric.
   - `A_av` gives the unit vector `e_av`.
3. **Φ on vertices (Lemma 2.2).** Well-definedness comes from vanishing on `P_{(a,b)}`, and push
   invariance from additivity. Constancy on `lk(q[(v,w)])` follows from the Link Lemma and vanishing
   on `P_{(v,w)}`.
4. **Descent (Theorem 3.1).** `Φ(A_av[(a,b)]) = 1`, so (CX0) forces `c > 0` there. Applying (CX1) to
   the one-vertex complex gives a push with strictly smaller c and the same Φ = 1, and iterating
   this contradicts well-foundedness.
   - The sphere form (Theorem 3.2) uses J ⊆ Q and `A_av ∈ P_σ` for each simplex σ of J.

The script checks steps 1–2 for n = 6, 7, 8 and all ordered quadruples, plus the identity
`φ_ab = χ_{z,u} − χ_{u,z}`. Its output is `antisym_clasp_output.txt`.
