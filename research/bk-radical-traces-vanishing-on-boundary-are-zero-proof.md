---
rg: 2
id: bk-radical-traces-vanishing-on-boundary-are-zero-proof
kind: route
title: Build the kernel ideal from compatible corner traces, kill the boundary corner by corner, and glue with Brown-Dadarlat
target: bk-radical-traces-vanishing-on-boundary-are-zero
requires:
  - stw07-separating-qd-quotients-force-quasidiagonality
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
  - brown-dadarlat-qd-extensions-and-k0-hahn-banach
  - moutzouris-faithful-trace-zero-class-both-signs
  - moutzouris-singular-subgroup-has-vanishing-trace
  - moutzouris-k0-killing-is-local
artifacts:
  - research/artifacts/bk-radical-trace-step-part2-2026-09-13.md
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

Full proof in Section 1 of the part-2 artifact.  Lemmas B and C are in part 1.

1. The corner kernels `N_k` are compatible.  The ideal `J` they generate meets
   each corner in `N_k` (Cohen factorisation in hereditary subalgebras), and
   `J ⊊ R`.
2. `R/J` has the approximate unit `q(e_k)`.  Its corners `e_k R e_k / N_k`
   carry faithful traces vanishing on the lifted boundary classes, and are UCT
   by two-out-of-three.
3. On each corner, Lemma B (from Moutzouris Theorem 4.1) gives an AF embedding
   killing the lifted classes.  Finite-stage compressions give models.  The
   proof of Moutzouris Proposition 3.5 extends them to `(R/J)~`.  Propositions
   3.3 and 3.2 turn this into a quasidiagonal embedding killing `q_*(H)`.
4. Lemma C (converse half of BD Proposition 4.6) makes `E/J` quasidiagonal,
   contradicting minimality of `R_qd(E)`.
5. For Corollary 6, states on `K_0` of unital real rank zero exact corners are
   induced by unique tracial states.  Moutzouris (2.5) and the sentence after
   it, citing his reference [24, Prop. 1.1.12], supply this, so a positive
   homomorphism gives a compatible family.
