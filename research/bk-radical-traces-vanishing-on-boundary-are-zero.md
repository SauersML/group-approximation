---
rg: 2
id: bk-radical-traces-vanishing-on-boundary-are-zero
kind: claim
title: In a Blackadar-Kirchberg counterexample with UCT quotients, no nonzero densely finite trace on the radical annihilates the boundary subgroup
distinct_from:
  bk-uct-counterexample-radical-not-projection-generated: that treats a radical containing one full projection, where a vanishing trace always exists; this is the general killing statement for any densely finite trace, with no projections assumed.
  stw07-quotient-trace-zero-nontorsion-class-is-killed: that balances models of one class through a trace-kernel quotient of the whole algebra; this contradicts minimality of the radical using traces on the radical itself.
  stw07-separating-qd-quotients-force-quasidiagonality: that puts the radical inside the kernels of UCT tracial states of the algebra; this constrains traces on the radical that need not extend to the algebra, such as Tr on the compacts inside the Toeplitz algebra.
artifacts:
  - research/artifacts/bk-radical-trace-step-part3-2026-09-13.md
  - research/artifacts/bk-radical-trace-step-part2-2026-09-13.md
  - research/artifacts/bk-radical-projection-trace-step-2026-09-13.md
---

**ESTABLISHED (Theorem 7 of the part-3 artifact, with Theorem 5 and Corollary 6
of part 2; lane proofs, not externally reviewed).**  Let `E` be separable,
nuclear and stably finite, with `R = R_qd(E)`.  Suppose `E/J` satisfies the UCT
for every ideal `J ⊆ R` of `E`, and put `H = ∂(K_1(E/R)) ⊆ K_0(R)`.

1. **Theorem 7.**  If `E` is not quasidiagonal, every densely finite lower
   semicontinuous trace `τ` on `R` with `τ^(H) = 0` is zero.
2. **Theorem 5 (special case).**  If `R` has an approximate unit of projections,
   no nonzero compatible family of bounded corner traces vanishes on `H`.
3. **Corollary 6.**  If `R` has real rank zero, every positive homomorphism
   `K_0(R) -> R` vanishing on `H` is zero.

Mechanism.
- The kernel ideal `J` of `τ` is proper.
- The pieces `her((h - 1/k)_+)` of `R/J` carry faithful bounded traces
  vanishing on the lifted boundary classes.
- Schafhauser's realisation (Moutzouris Theorem 4.1) kills those classes on the
  unitised pieces.
- Moutzouris' local-approximation scheme assembles a quasidiagonal embedding of
  `R/J` killing `q_*(H)`.
- Brown--Dadarlat Theorem 3.4 makes `E/J` quasidiagonal, contradicting
  minimality.

Meaning: tracial states of `E` annihilate the boundary automatically.  The
content is for traces on `R` not coming from `E`, like `Tr` on `K ⊆ T`.  In a
counterexample each densely finite one must see an index.

Limits.
- Traces on proper ideals of `R` (for example the traced compact ideals of
  `stw07-qd-radical-criterion-compact-open`) are not densely finite on `R`, and
  are unconstrained here.
- An AF algebra with lexicographically chained `K_0 = ⊕ Z e_n` has no nonzero
  densely finite trace at all.

See `bk-rr0-uct-stably-finite-algebras-are-qd` for the open real rank zero
residual.
