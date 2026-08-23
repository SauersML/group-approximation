---
rg: 2
id: partial-isometry-gram-state-collapses-lin-corners
kind: claim
title: A partial-isometry Gram state collapses all of Lin's spectral layers to the common source
distinct_from:
  lin-near-synchrony-selects-one-state-corner: that treats an arbitrary positive density and has no relative marked-mass floor; this specializes to the Gram vector already supplied by the D8 partial swap and proves that its spectral-layer carrier is fixed with the full D8 source mass.
  dihedral-spin-packet-supplies-common-partial-swap: that authenticates the partial isometry and its source-mass floor in an exactified finite packet; this identifies the same source projection as the unique positive-measure corner in Lin's synchronous rounding.
  lin-canonical-dilation-twirls-unprotected-left-carriers: that computes the remaining loss when a left operator is carried through Theorem 5.1; this removes the preceding spectral-corner mass loss but does not solve that left-covariance problem.
---

Let `(M_d,tau)` have normalized trace, let `S in M_d` be a nonzero partial
isometry, and put

```text
q=S^*S,       r=SS^*,       s=tau(q)=tau(r)>0.          (LGS1)
```

The normalized Gram vector `xi=s^(-1/2)S in L^2(M_d,tau)` has a
tracially embeddable standard form whose positive density is

```text
sigma=s^(-1/2)q.                                      (LGS2)
```

Indeed, extend `S` to a unitary `U` with `Uq=S`.  For every pair of left
and right operators `A,B`,

```text
<xi,L_A R_B xi>
 =s^(-1)tau(S^*ASB)
 =<sigma,L_(U^*AU) R_B sigma>.                        (LGS3)
```

Lin's Proposition A.8 and Theorem 4.1 use precisely the spectral layers

```text
P_lambda=chi_[sqrt(lambda),infinity)(sigma).
```

For `(LGS2)`, apart from the measure-zero endpoint `lambda=0`,

```text
P_lambda=q       for 0<lambda<=1/s,
P_lambda=0       for lambda>1/s.                      (LGS4)
```

Thus every positive-measure synchronous component produced by Lin lives on
the **same** corner `q`; its probability density is `tau(P_lambda)=s` on an
interval of length `1/s`.  There is no carrier selection and no loss of
mass.

In the D8 common-swap packet, `q` is the decoded source projection of the
one literal off-diagonal block `S_D8`.  Hence the D8 estimate

```text
tau(q)>=gamma tau((I-J)/2)-o(1)                       (LGS5)
```

passes unchanged through Lin's Theorem 4.1 when the rounded strategy is the
normalized one-Gram strategy of `S_D8`.  This eliminates the arbitrary-
density mass obstruction for the intended compiler state.

It does not prove `(CPS9)` or `(CPS12)`.  The unitary completion `U` in
`(LGS3)` is representation-dependent, and it conjugates the left context
operators.  Theorem 5.1 protects the right/opposite algebra, while
`lin-canonical-dilation-twirls-unprotected-left-carriers` shows that this
conjugated left carrier is Reynolds-twirled unless an additional covariance
estimate is supplied.  The remaining Lin-to-Cairn seam is therefore
sharper: **mass and a common spectral corner are automatic for the D8 Gram
state; finite-word authentication of the polar conjugacy and its left
payload is not.**
