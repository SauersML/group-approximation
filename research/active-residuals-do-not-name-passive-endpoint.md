---
rg: 2
id: active-residuals-do-not-name-passive-endpoint
kind: claim
title: Identical active residual carriers do not name the passive congruence endpoint
distinct_from:
  cuspidal-redistribution-refutes-regular-core-orbit-basin: that gives two exact endpoints over one literal BS core; this adjoins the same nonzero compressed boundary cell to both and proves that even the full active residual polar data remain identical.
  bs14-bounded-moments-cannot-extract-congruence-level: that rules out fixed scalar moment fingerprints; this is an operator-valued residual-carrier blindness theorem at one common moving core.
  weil-reservoir-mixing-has-energy-paid-completion: that completes an authenticated active Weil reservoir; this proves such a reservoir cannot also choose the exact passive endpoint type.
---

**ESTABLISHED.**  Let `A=PSL_2(Z[1/2])` in the Iwahori presentation and
`B=<R,S>`.  There are two sequences of near representations

```text
T_p=(X_p,R_p,S_p),             T_p'=(X_p',R_p,S_p)       (ARP1)
```

on the same spaces, with the following simultaneous properties.

1. Their exact BS cores are literally equal.
2. Their two cubic residual operators are literally equal and nonzero:

   ```text
   (X_pS_p^2)^3-1=(X_p'S_p^2)^3-1,
   (X_pR_pS_p)^3-1=(X_p'R_pS_p)^3-1.                    (ARP2)
   ```

   Consequently every singular value, polar partial isometry, carrier
   projection, mutual principal-angle operator, and thresholded active
   source obtained from the two residuals is identical for `T_p,T_p'`.
3. The common nonzero residual is a sum of `k_p` copies of one fixed
   authenticated even-Weil boundary cell, where one may arrange

   ```text
   k_p -> infinity,             k_p/d_p ->0.             (ARP3)
   ```

   Restoring the same `k_p` lines completes both active cells, and their
   Frobenius cubic energy is bounded above and below by constant multiples
   of `k_p`.  In particular the normalized two-cubic energy tends to zero.
4. Nevertheless one constant `c>0` satisfies

   ```text
   inf_(U in {R_p,S_p}') ||X_p'-U X_p U^*||_2 >= c-o(1). (ARP4)
   ```

Thus an authenticated active boundary reservoir does not authenticate the
global endpoint on the passive regular face.  A reverse construction may
restore the common active cell locally, but it must retain or separately
correct the supplied passive involution.  Replacing the passive complement
by the endpoint type named by the core, by the residual carriers, or by any
regular-face spectral decomposition is invalid.

This does not obstruct flexible repair: each sequence has its own exact
completion, obtained by restoring the common boundary line and retaining
its own passive exact endpoint.  It rules out only the stronger and tempting
factorization

```text
(exact core + active residual polar data)
       -> one global congruence endpoint type.                         (ARP5)
```

The surviving reverse theorem must be triangular: local active-cell
restoration plus an adaptive passive-endpoint correction which uses `X_p`
outside the `o(d_p)` active hull.

DERIVATION
active-residual-passive-blindness-proof
