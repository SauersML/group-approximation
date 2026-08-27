---
rg: 2
id: pauli-overlap-yields-positive-spectral-corner
kind: claim
title: The compulsory Pauli cross-Gram overlap contains a fixed positive spectral corner
distinct_from:
  soft-block-mass-yields-fractional-branch: that extracts a branch from one compressed block; this extracts an oriented collision corner from the sum of two cross-Gram energies.
  mixed-relations-force-holonomy-or-transverse-recovery: that must analyze the mixed relators on the extracted corner; this supplies the corner with explicit constants.
---

Let `X_0,X_1` be the two contractions of
`pauli-packet-incoming-mass-exceeds-corner-capacity`.  Then

```text
||X_1^*X_0||_2^2 + ||X_0^*X_1||_2^2 >= 5/32.          (PSC1)
```

Hence for one orientation `(i,j)` with `i!=j`, the contraction

```text
Y=X_j^*X_i
```

satisfies `tau(Y^*Y)>=5/64`.  Put

```text
R=1_[5/128,1](Y^*Y).                                  (PSC2)
```

Then

```text
tau(R) >= 5/123,                                      (PSC3)
Y^*Y R >= (5/128) R.                                  (PSC4)
```

Indeed, writing `p=tau(R)` and using `0<=Y^*Y<=1`,

```text
5/64 <= tau(Y^*Y) <= (5/128)(1-p)+p,
```

which rearranges to `p>=5/123`.  Everything is canonical after splitting
into the two possible orientations, and all constants are independent of
matrix dimension.

Thus the compulsory overlap already supplies the fixed-density corner that
the holonomy-or-transverse route needs.  The remaining open statement is not
corner extraction; it is proving that the mixed atlas relators force either
nontrivial holonomy or recovery of the same centered carrier in both
transverse descendants on this corner.

