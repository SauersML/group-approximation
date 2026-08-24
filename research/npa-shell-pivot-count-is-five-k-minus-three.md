---
rg: 2
id: npa-shell-pivot-count-is-five-k-minus-three
kind: claim
title: Every new moment class but four factors through two nonresidual basis words
artifacts:
  - research/artifacts/npa-critical-face-dimension-law-audit-2026-08-23.md
---

Call a level-`k` basis word `p = (a,b)` **residual** when it is the identity, or
is one-party with its nonempty alternating word ending in `1`; a nonresidual `p`
carries a canonical relation `R_p` in the range of `N_k` with

```text
R_p = e_p + (terms of strictly smaller total word degree),
```

namely the trailing-zero relation `T_p` when some party ends in `0`, and the
dressing `D_[(w_a, w_b)]` when `p = (w_a 1, w_b 1)`.

The claim: of the `5k+1` moment classes newly available at level `k`, exactly
four fail to factor as `p* q` with `p, q` nonresidual level-`k` words and no
cancellation, and, up to simultaneous reversal and party swap, they are

```text
U_1 = (empty, r_(2k-1)),   U_2 = (empty, 0 r_(2k-1)),
U_3 = ((0), r_(2k-1)),     U_4 = ((1), r_(2k-1)).
```

For each of the other `5k-3` classes the pairing `R_p^T Gamma_k(y) R_q` is a row
of `Phi_k` in which that class is the unique term of maximal degree, with
coefficient `1`.  Hence the shell contributes `5k-3` unit-triangular pivots.

## Attempts

The cut construction is written and is close to complete.  For a new class
`(alpha, beta)` with `a = |alpha| <= b = |beta|`, cut after `i` and `j` letters
and set `p = (rev(alpha_(<i)), rev(beta_(<j)))`, `q = (alpha_(>=i), beta_(>=j))`;
alternation of the original words forbids cancellation, so `p* q = (alpha,beta)`.
At degree `2k-1` take `|p| = k-1`, `|q| = k`, with `(i,j) = (a-1, k-a)` when
`a >= 2`, and with `(0, k-1)` or `(1, k-2)` according to the first letter of
`beta` when `a = 1`.  At degree `2k` take `|p| = |q| = k` with
`(i,j) = (a-1, k-a+1)` when `a >= 2`, and `(0,k)` when `a = 1` and `beta` starts
in `0`.

Two branches are asserted rather than exhausted: degree `2k` with `a = 1` and
`beta` starting and ending in `1`, where the claim is that every split leaves a
residual factor and the failures are exactly `U_3, U_4`; and degree `2k` with
`a = 0`, where the claim is that every split leaves a residual factor, giving
`U_2` modulo reversal.  Writing those two exhaustions out is the whole remaining
gap, and each is a finite parity argument over the position of the cut.

Numerically the classification holds for `k = 3..12` -- exactly `5k+1` new
classes, exactly four exceptions, restricted pivot rank exactly `5k-3` -- but the
verifier that reports this was supplied without the two modules it imports and
could not be run here.
