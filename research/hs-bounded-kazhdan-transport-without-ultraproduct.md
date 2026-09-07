---
rg: 2
id: hs-bounded-kazhdan-transport-without-ultraproduct
kind: claim
title: One-sided Kazhdan transport holds for Hilbert-Schmidt bounded sequences
distinct_from:
  kazhdan-asymptotic-commutant-transport: that is the printed theorem, for asymptotic commutants of sequences bounded in operator norm; this enlarges the commutant to all sequences bounded in normalized Hilbert-Schmidt norm, which is a strictly weaker boundedness hypothesis, and the printed theorem is its restriction.
  kazhdan-projection-finite-target-calculus: that is the exact one-sided order and commutation calculus for the Kazhdan projection in a finite C*-target; this is the sequence-level transport statement that consumes it.
  kazhdan-projection-rounding: that is a quantitative one-step rounding inside a single finite tracial algebra; this is an asymptotic statement about a sequence of matrix algebras and a compressor.
artifacts:
  - research/artifacts/shorter-proofs-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `L <= G` have property (T), let `u in G` satisfy `uLu^(-1) <= L`, and let
`(V_n)` be an operator-norm asymptotic representation of `G` in `U(d_n)`.
Define

```text
C_2^2(V,L) = { (x_n) : sup_n ||x_n||_2 < infinity,
               ||Ad(V_n(l))x_n - x_n||_2 -> 0 for every l in L }.
```

Then

```text
Ad(V(u)) ( C_2^2(V,L) ) = C_2^2(V,L).
```

The printed theorem is the restriction to sequences with
`sup_n ||x_n||_op < infinity`, and that restriction is strict, since
`||.||_2 <= ||.||_op` with no reverse bound independent of dimension.

The proof of the printed theorem already gives this: every estimate reaches
`x_n` through operators bounded on the Hilbert space
`(M_(d_n),||.||_2)`, so the constant `c` in it may be read as
`sup_n ||x_n||_2`.

**Formalization note.**  The Lean marker on the printed theorem certifies the
operator-norm-bounded form, so it does not transfer to this statement.
