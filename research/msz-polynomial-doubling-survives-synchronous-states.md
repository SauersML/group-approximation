---
rg: 2
id: msz-polynomial-doubling-survives-synchronous-states
kind: claim
title: The MSZ polynomial doubling contraction survives synchronous states
artifacts:
  - research/artifacts/mehta-slofstra-zhao-positivity-ingestion-2026-08-20.md
distinct_from:
  msz-polynomial-doubling-star-algebra-compiler: that gives the exact recurrence and its tracial collapse; this proves the same exponential-versus-polynomial ledger without assuming that the left marginal is tracial.
  classical-pcp-gap-is-not-tracial-pvm-gap: that forbids classical rounding of arbitrary exact quantum solutions; this uses operator synchrony directly and performs no classical rounding.
---

Use the compiler of `msz-polynomial-doubling-star-algebra-compiler`.  Suppose
`m notin L`, `phi` is an `(epsilon,X)`-synchronous state on

```text
C Z_2^(*X) tensor C Z_2^(*X),
```

and its left marginal `tau` is an `(epsilon,R_m)`-state.  Then fixed positive
integers `Gamma,k`, independent of `m`, satisfy

```text
||P_tilde_0||_tau <= Gamma m^k sqrt(epsilon).                    (MSY1)
```

More precisely, synchrony controls the conjugation by the length-`4n+1`
word `X_tilde_n` and the mixed cross term in the square of
`P_tilde_n+X_tilde_n P_tilde_n X_tilde_n`.  Combining those estimates with
the polynomial `R_m`-decomposition gives

```text
||P_tilde_n||_tau
 <= 2^(-1/2)||P_tilde_(n+1)||_tau
    +2^(-1/2)(C+25)((n+1)m)^k sqrt(epsilon).                     (MSY2)
```

Iteration proves `(MSY1)` because `P_tilde_n` is a contraction and
`sum_n n^k 2^(-n/2)` converges.

This closes the analytic state-transfer issue for the additive doubling
tape.  It does not turn its projection identity into group words, and hence
does not close `constant-depth-schur-lift-of-doubling-tape` or the final
nonhyperlinear-group goal.
