---
rg: 2
id: bk-radical-traces-vanishing-on-boundary-are-zero
kind: claim
title: In a Blackadar-Kirchberg counterexample with UCT quotients, no nonzero compatible corner trace of a projection-rich radical vanishes on its boundary subgroup
distinct_from:
  bk-uct-counterexample-radical-not-projection-generated: that treats a radical containing one full projection; this treats radicals with an approximate unit of projections, where no full projection need exist, given a compatible family of corner traces.
  stw07-quotient-trace-zero-nontorsion-class-is-killed: that balances models of one class through a trace-kernel quotient of the whole algebra; this contradicts minimality of the radical using traces on corners of the radical itself.
artifacts:
  - research/artifacts/bk-radical-trace-step-part2-2026-09-13.md
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

**ESTABLISHED (Theorem 5 and Corollary 6 of the part-2 artifact; lane proof, not
externally reviewed).**  Let `E` be separable, nuclear and stably finite, with
`R = R_qd(E)`.  Suppose `E/J` satisfies the UCT for every ideal `J ⊆ R`, and `R`
has an increasing approximate unit of projections `(e_k)`.  Let
`H = ∂(K_1(E/R)) ⊆ K_0(R)`.

1. **Theorem 5.**  Suppose bounded traces `τ_k` on `e_k R e_k` are compatible
   under restriction, not all zero, and satisfy `τ^(H) = 0`.  Then `E` is
   quasidiagonal.
2. **Corollary 6.**  If `R` has real rank zero and `E` is not quasidiagonal,
   every positive homomorphism `K_0(R) -> R` vanishing on `H` is zero.

Mechanism.
- The kernels of the `τ_k` generate an ideal `J ⊊ R` whose quotient corners
  carry faithful traces vanishing on the image of `H`.
- Schafhauser's realisation kills that image on each corner.
- Moutzouris' local-approximation scheme assembles the corner models into a
  quasidiagonal embedding of `R/J` killing the whole boundary.
- Brown--Dadarlat Theorem 3.4 makes `E/J` quasidiagonal, contradicting
  minimality of the radical.
- In real rank zero, positive functionals on `K_0` of a unital corner come from
  unique traces, which supplies the compatible family.

Limit: an AF algebra with lexicographically chained `K_0 = ⊕ Z e_n`
(`m e_n ≤ e_(n+1)` for all `m`) has no nonzero densely finite trace.  So the
theorem is blind to non-archimedean exhaustions.  See
`bk-rr0-uct-stably-finite-algebras-are-qd`.
