---
rg: 2
id: bk-radical-traces-vanishing-on-boundary-are-zero-proof
kind: route
title: Build the kernel ideal of the trace, kill the boundary on bounded hereditary pieces, and glue with Brown-Dadarlat
target: bk-radical-traces-vanishing-on-boundary-are-zero
requires:
  - stw07-separating-qd-quotients-force-quasidiagonality
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
  - brown-dadarlat-qd-extensions-and-k0-hahn-banach
  - moutzouris-faithful-trace-zero-class-both-signs
  - moutzouris-singular-subgroup-has-vanishing-trace
  - moutzouris-k0-killing-is-local
artifacts:
  - research/artifacts/bk-radical-trace-step-part3-2026-09-13.md
  - research/artifacts/bk-radical-trace-step-part2-2026-09-13.md
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

Theorem 7 is proved in Section 1 of the part-3 artifact, Theorem 5 and
Corollary 6 in part 2, and Lemmas B and C in part 1.

1. `J = {a ∈ R : τ(a*a) = 0}` is a proper closed ideal.
2. For a strictly positive `h`, `τ` is bounded on `C_k = her((h - 1/k)_+)`, by
   Fact T1 of `research/artifacts/bk-t1-spectrum-simple-reduction-2026-09-12.md`
   applied to `(h - 1/(2k))_+ ∈ Ped(R)`.  The pieces `C_k/(C_k ∩ J)` of `R/J`
   carry faithful bounded traces vanishing on the lifted boundary classes, and
   are UCT by two-out-of-three.
3. Lemma B, from Moutzouris Theorem 4.1, applies to the unitised pieces with
   the faithful state `½ τ̄_k/||τ̄_k|| + ½ χ`, and gives AF embeddings killing
   the lifted classes.  Finite-stage compressions, Arveson extension and the
   proof of Moutzouris Proposition 3.5, followed by Propositions 3.3 and 3.2,
   give a quasidiagonal embedding of `R/J` killing `q_*(H)`.
4. Lemma C (converse half of BD Proposition 4.6, using BD Theorem 3.4) makes
   `E/J` quasidiagonal, contradicting minimality of `R_qd(E)`.
5. Corollary 6: states on `K_0` of unital real rank zero exact corners are
   induced by unique tracial states (Moutzouris (2.5) and the sentence after
   it), so a positive homomorphism gives a compatible family.  Compatible corner
   traces define a densely finite lower semicontinuous trace.
