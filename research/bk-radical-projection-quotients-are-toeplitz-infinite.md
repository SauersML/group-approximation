---
rg: 2
id: bk-radical-projection-quotients-are-toeplitz-infinite
kind: claim
title: Every quotient of the radical of a UCT Blackadar-Kirchberg counterexample is compact somewhere, and each projection-generated one makes the corresponding quotient of the algebra infinite
distinct_from:
  bk-uct-counterexample-radical-not-projection-generated: that is the case K = 0, where infiniteness of E contradicts stable finiteness; this constrains every proper quotient of the radical.
  stw07-qd-radical-criterion-compact-open: that says the radical itself has a compact open primitive subset; this says every quotient of the radical by a proper ideal does.
  bk-primitive-quotients-qd-or-traceless-force-qd: that finds traced non-quasidiagonal primitive quotients over a compact open set; this shows that projection-generated quotients of the radical give non-stably-finite quotients of the algebra.
artifacts:
  - research/artifacts/bk-radical-trace-step-part4-2026-09-13.md
  - research/artifacts/bk-radical-trace-step-part3-2026-09-13.md
---

**ESTABLISHED (Theorems 8, 9 and Corollaries 10, 11 of the part-4 artifact;
lane proofs, not externally reviewed).**  Let `E` be separable and nuclear,
`R = R_qd(E)`, and `H = ∂(K_1(E/R))`.

1. **Theorem 8 (no UCT needed).**  For every ideal `K ⊊ R` of `E`, `Prim(R/K)`
   has a nonempty compact open subset.
2. **Theorem 9.**  Suppose `E` is stably finite and not quasidiagonal, with
   `E/J` UCT for every ideal `J ⊆ R`.  If `K ⊊ R` and `R/K` contains a full
   projection, then `R/K` is not stably finite or `q_*(H)` contains a nonzero
   positive class.  In either case `E/K` is not stably finite.
3. **Type I (Corollary 10).**  In a type I counterexample, every finite set of
   elementary closed points of `Prim(R)` is seen with strictly positive rank by
   one class of `H`.  Positivity of that class must then fail at non-closed,
   Toeplitz-like points.
4. **Real rank zero (Corollary 11).**  No quotient `R/K`, `K ⊊ R`, carries a
   nonzero positive homomorphism `K_0(R/K) -> R` annihilating the image of `H`.

Mechanism.
- Theorem 8: the spectral extension theorem applied to
  `0 -> R/K -> E/K -> E/R -> 0`, plus minimality of the radical.
- Theorem 9: a trace on the full corner of `R/K` annihilating `q_*(H)`
  (Lemma A) pulls back to a densely finite trace on `R` annihilating `H`.
  `bk-radical-traces-vanishing-on-boundary-are-zero` forbids that.  Spielberg's
  criterion converts the surviving positive class into infiniteness of `E/K`.

So a glued UCT counterexample hides its radical under Toeplitz-infinite
quotients.
