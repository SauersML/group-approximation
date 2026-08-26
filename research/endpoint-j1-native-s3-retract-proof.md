---
rg: 2
id: endpoint-j1-native-s3-retract-proof
kind: route
title: Restrict both zero-prefix Whiteheads to the orthogonal one-cylinder corner
target: endpoint-j1-enlargement-has-native-s3-retract
requires:
  - endpoint-external-subgroup-has-native-s3-retract
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
---

For a depth-`k` zero-prefix Whitehead, write

```text
e_k=s_(0^k)t_(0^k),
c_k=s_(0^(k+1))t_(0^k),
d_k=s_(0^k)t_(0^(k+1)).                              (1)
```

Its nonidentity coefficients lie in the two-sided support of `e_k`, which
is contained in `p=s_0t_0`.  The endpoint `P` uses `k=2`; the first prefix
Whitehead `J_1` uses `k=1`.  With `q=s_1t_1`, the Leavitt prefix relations
give

```text
pq=qp=0,          qc_k=c_kq=qd_k=d_kq=0,
qe_k=e_kq=0.                                           (2)
```

Therefore the scalar projection `qI` commutes with both Whiteheads, and
their two corner restrictions are the identity `qI`, proving `(EJR4)`.
The constant roots commute with `qI`, and multiplication gives `(EJR5)`.

Since `q!=0`, the prime subring `{0,q}` of `qRq` is `F_2`.  On coordinates
`7,8`, the two restrictions in `(EJR5)` are

```text
[[q,q],[0,q]],             [[q,0],[q,q]].              (3)
```

They are two distinct involutions whose product has order three, and their
six products are distinct.  Thus they generate `GL_2(F_2)`.

Because `qI` commutes with every generator of `G_1`, corner restriction

```text
pi_1:G_1 -> GL_20(qRq),       g |-> (qI)g(qI)          (4)
```

is a homomorphism.  It kills `P,J_1` and is injective on `N=<n,m>`.
Identifying `pi_1(N)` with `N` proves the split retraction `(EJR2)`.

The two MSI artifacts replay `(2)--(3)` in faithful sparse normal form and
enumerate the stated depth-nine relators.  The finite search is only a
calibration; `(4)` proves compatibility with every word relation.

