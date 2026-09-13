---
rg: 2
id: bk-uct-counterexample-radical-not-projection-generated-proof
kind: route
title: Kill the radical's boundary through a trace on its full corner and contradict minimality
target: bk-uct-counterexample-radical-not-projection-generated
requires:
  - stw07-separating-qd-quotients-force-quasidiagonality
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
  - brown-dadarlat-qd-extensions-and-k0-hahn-banach
  - moutzouris-singular-subgroup-has-vanishing-trace
  - moutzouris-faithful-trace-zero-class-both-signs
artifacts:
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

Full proof in Section 2 of the artifact, with Lemmas A--C in Section 1.

1. `E/R` is quasidiagonal (radical theorem) and UCT.  Spielberg's criterion (BD
   Proposition 4.1, recorded in `brown-dadarlat-ext-trivial-class-gives-qd-extension`)
   makes `H = ∂(K_1(E/R))` singular in `K_0(R)`.
2. Lemma A (Moutzouris Proposition 2.6 and Lemma 2.12, with traces from states
   on exact algebras) gives a tracial state `τ` on `D = pM_n(R)p` with
   `τ^(H) = 0`.  Its kernel corresponds to an ideal `J ⊊ R` of `E`.
3. `R/J` is UCT by two-out-of-three from `E/J` and `E/R`.  Lemma B, from
   Moutzouris Theorem 4.1 applied to the strict-order dimension group
   `(K_0 ⊗ Q)/(H ⊗ Q)` with its unique state, embeds `D/N` unitally in a simple
   AF algebra, killing `q_*(H)`.  Brown's stable isomorphism carries this to
   `R/J`.
4. Lemma C, the converse half of BD Proposition 4.6 using BD Theorem 3.4 and
   Lemma 4.5, makes `E/J` quasidiagonal.  The minimality of `R` gives `R ⊆ J`,
   a contradiction.
