---
rg: 2
id: labelled-pvm-branch-gram-gives-lin-corner
kind: claim
title: Orthogonal labelled branches form one exact Lin common-PVM Gram corner
artifacts:
  - research/artifacts/labelled-pvm-lin-gram-audit-2026-08-23.md
distinct_from:
  partial-isometry-gram-state-collapses-lin-corners: that starts from one already authenticated partial isometry and computes its two-point Lin density; this constructs the common Gram contraction from many labelled branches and treats arbitrary spectral density.
  orthogonal-hecke-row-packs-common-source-energy-into-one-root: that packs covariance defects as one coefficient but leaves their size unauthenticated; this discards off-label blocks analytically and makes covariance exact on the retained Gram operator.
  common-source-covariance-locks-binary-marginals: that estimates transported marginal traces from supplied covariance rows; this constructs an exactly label-intertwining one-state corner and identifies the sole mass lost in obtaining it.
---

**ESTABLISHED.**  Let `(E_i)` and `(F_i)` be finite orthogonal projection
families in a finite tracial matrix algebra, and let `T_i` be contractions.
Put

```text
G=sum_i F_iT_iE_i,        E=sum_iE_i,       F=sum_iF_i. (LBG1)
```

Then

```text
G^*G=sum_i E_iT_i^*F_iT_iE_i<=E,
GG^*=sum_i F_iT_iE_iT_i^*F_i<=F,                       (LBG2)

F_iG=GE_i=F_iT_iE_i,
||G||_2^2=sum_i||F_iT_iE_i||_2^2.                     (LBG3)
```

In particular `G` is one contraction carrying the whole labelled PVM
exactly.  If every displayed branch is a source-saturating partial isometry,
then `G` is a partial isometry with source `E`.

For nonzero `G=U|G|`, every spectral layer `P_lambda` of
`|G|/||G||_2` commutes with every `E_i`, and on every layer bounded away from
zero,

```text
F_iUP_lambda=UE_iP_lambda.                             (LBG4)
```

Thus Lin's spectral layering yields a common labelled-PVM corner of this
same one Gram state; it does not reintroduce independent context gauges.

When complete PVMs are indexed by two binary labels, `T_i=T`, and

```text
A_j=sum_a a_jF_a,       Z_j=sum_a a_jE_a,
D_j=A_jT-TZ_j,
```

block orthogonality gives the sharp estimates

```text
4||T-G||_2^2
 <=sum_(j=X,Y)||D_j||_2^2
 <=8||T-G||_2^2.                                      (LBG5)
```

If `T^*T=Q`, then

```text
||G||_2^2>=tau(Q)-(1/4)sum_j||D_j||_2^2,
[Q,Z_j]=D_j^*T-T^*D_j,
||[Q,Z_j]||_2<=2||D_j||_2.                            (LBG6)
```

There is a hypothesis-minimal binary specialization which does **not**
assume that two source observables commute.  For arbitrary involutions
`A_X,A_Y,Z_X,Z_Y`, a contraction `T`, and the two spectral PVMs of `A_X`
and `Z_X`, set

```text
G_X=sum_(e=+-1) ((1+e A_X)/2) T ((1+e Z_X)/2),
D_j=A_jT-TZ_j.                                        (LBG7)
```

Then

```text
A_XG_X=G_XZ_X,
||T-G_X||_2^2=(1/4)||D_X||_2^2.                      (LBG8)
```

If `T^*T=Q`, Pythagoras gives the exact mass identity

```text
||G_X||_2^2=tau(Q)-(1/4)||D_X||_2^2.                 (LBG9)
```

The unanchored endpoint stays on this same Gram operator with

```text
||A_YG_X-G_XZ_Y||_2<=||D_X||_2+||D_Y||_2.            (LBG10)
```

If `[A_X,A_Y]=0` and `R_Y=A_YG_X-G_XZ_Y`, exact anchored covariance also
gives

```text
G_X[Z_X,Z_Y]=-A_XR_Y+R_YZ_X,
||G_X[Z_X,Z_Y]||_2<=2||R_Y||_2.                      (LBG11)
```

Thus a single binary anchor always supplies the labelled source PVM.  No
joint source PVM for `(Z_X,Z_Y)` is needed: positive `G_X` mass plus the
unanchored endpoint and role/return covariance on this very same `G_X` feed
the positive-Gram Lin corner.

Consequently the source-commutator terms in `(SEC4)` are redundant after
exact common Gram and covariance.  More importantly, on a role amplification
of the three `S3` charts, `(LBG1)` converts every covariance encoded by its
labels to one exactly covariant Gram operator.  If the labels already contain
the complete packet, the downstream finite-strategy argument only needs a
scalar mass floor

```text
||G||_2^2>=gamma tau(Q)-K E_rel-o(1).                 (LBG12)
```

This claim does not prove `(LBG12)` and, in the complete-label formulation,
assumes that the labelled source and target PVMs have already been constructed
on the same Hilbert space.  Those hypotheses are load-bearing.  In the
one-bit formulation `(LBG7)--(LBG11)`, the remaining unlabelled packet
covariance must instead be authenticated on the same `G_X`; a mass floor
alone is insufficient.  Even complete PVMs and unitary branches admit an
exact cyclic-shift model with `G=0`.  Lin's theorem supplies a spectral corner
of a positive `G`; it supplies neither positive mass nor the genuinely mixed
same-Gram covariance as ordinary group-word consequences.
