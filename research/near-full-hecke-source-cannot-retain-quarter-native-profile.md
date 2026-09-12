---
rg: 2
id: near-full-hecke-source-cannot-retain-quarter-native-profile
kind: claim
title: A quarter-profile subcut must discard one third of the balanced Hecke source
artifacts:
  - research/near-full-hecke-quarter-profile-loss-proof.md
distinct_from:
  full-hecke-quarter-source-equalizes-selector-ranks: that computes the two balanced source marginals on the whole signed Hecke source; this gives the sharp loss needed to change the second compressed marginal back to one quarter on any subcut.
  center-chain-common-source-authenticates-native-covariances: that asks ordinary relation defects to produce model-dependent native occurrence charts with vanishing ambient loss; this rules out obtaining its second source chart by merely taking a near-full reducing subprojection of the fixed Hecke source.
  vanishing-loss-center-chain-authentication-hits-affine-firewall: that uses both selector rows and a shared reservoir gauge to force a row-error floor; this is a one-row support-rank obstruction which needs neither a target transport nor a gauge comparison.
---

**ESTABLISHED SHARP SOURCE-LOSS FENCE.**  Retain the signed Hecke source

```text
Q=e_(L_0,lambda_0),                 q=tau(Q)>0,
```

and the second native source sign

```text
t=x_69(a_3)
```

from `b2-b3-pair-full-hecke-four-native-sectors`.  On `Q`, the two signs of
`t` have equal trace:

```text
tau(Q(1+t)/2)=tau(Q(1-t)/2)=q/2.                    (QPL1)
```

Let `E<=Q` be any nonzero projection, with no invariance assumption, and put

```text
beta=tau(E),                 eta=tau(Q-E)=q-beta,
Q_-=Q(1-t)/2,
rho=tau(EQ_-E)/beta.                                 (QPL2)
```

If `rho=1/4`, then

```text
eta>=q/3,                    beta<=2q/3.             (QPL3)
```

The constant is sharp: retain all of the positive half of `Q` and exactly
one third of its negative half.  More generally, if

```text
|rho-1/4|<=zeta<1/4,
```

then

```text
eta/q >= (1-4zeta)/(3-4zeta).                       (QPL4)
```

Thus a sequence of arbitrary subcuts whose discarded ambient trace tends
to zero has compressed second-source negative mass tending to `1/2`, never
to the native `1/4` profile.  If `E` reduces `t`, `rho` is exactly the
negative spectral fraction of `t|_(EH)`.  In the canonical trace,
`q=1/8192`, so an exact quarter-profile cut discards at least

```text
1/24576                                                    (QPL5)
```

of the ambient normalized trace.

This is a scoped obstruction, not a refutation of the full common-source
authentication claim.  That claim may still try to build a moving native
source chart whose occurrence is related to `Q` by additional ordinary
words and whose constant loss is charged to full-presentation defects.
What `(QPL3)--(QPL4)` forbids is treating a near-full subprojection of the
fixed `Q` chart itself as the required quarter-profile second native source,
even before one asks that the subprojection reduce the native sign.  Such a
construction has a fixed rank loss before any target,
cross-Gram, order-seven, or shared-gauge issue is considered.

DERIVATION
near-full-hecke-quarter-profile-loss-proof
