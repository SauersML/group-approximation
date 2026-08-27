---
rg: 2
id: neutral-weil-mixed-carrier-energy-tends-to-355-over-64
kind: claim
title: The symmetric neutral Weil structural energy tends to 355 over 64
distinct_from:
  neutral-weil-symmetric-retraction-is-double-neutral: that reduces the post-rounding defect to a determinant-neutral carrier of dimension at most thirty-four; this evaluates that carrier asymptotically and finds a positive limit.
  even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two: that computes only the principal angle of the two pre-rounding cubic carriers; this evaluates both reconstructed structural words after rounding.
  deleted-fixed-line-first-cubic-has-explicit-positive-spectrum: that evaluates a cubic before it is rounded away; this proves that a fixed amount of its energy reappears in inversion and BS covariance.
---

Use the canonical symmetric retraction of
`neutral-weil-symmetric-retraction-is-double-neutral` at primes
`p=1 mod 8`, and write `u_p,v_p` for its inversion and BS structural
words.  Then

```text
rank(u_p-1)<=4,                 rank(v_p-1)<=4,        (NMC1)

||u_p-1||_F^2  -> 79/32,
||v_p-1||_F^2  -> 197/64.                              (NMC2)
```

In particular

```text
||u_p-1||_F^2+||v_p-1||_F^2 -> 355/64.                (NMC3)
```

Thus the doubly determinant-neutral branch has a uniform positive
unnormalized Frobenius floor for all sufficiently large primes.  No
infinite `p=1 mod 8` subsequence of the canonical symmetric retraction can
make the structural energy tend to zero.  The old thirty-four-dimensional
carrier bound is very nonsharp: after the exact word cancellations, each
of the two residuals has only two conjugate eigenvalue pairs.

More precisely, the four nontrivial eigenvalues converge to the roots of

```text
P_u(z)=z^4-(177/64)z^3+(247/64)z^2-(177/64)z+1,
P_v(z)=z^4-(315/128)z^3+(437/128)z^2-(315/128)z+1.    (NMC4)
```

Both reciprocal polynomials have four nonidentity unit-circle roots, so
the limiting charge is spectral rather than determinantal.  This closes
the requested scalar computation for the actual canonical neutral Weil
packet.  It does not by itself prove a packet-independent flexible repair
inequality for arbitrary mixtures.
