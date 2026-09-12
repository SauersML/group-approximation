---
rg: 2
id: compressed-s-rank-three-lift-has-no-one-sided-inverse
kind: claim
title: The compressed rank-three s-lift has no one-sided inverse in the ambient corner
distinct_from:
  leavitt-rank-three-lift-has-no-one-sided-inverse: that explicitly states the compressed conclusion for the t-lift; this records and proves the symmetric compressed s-lift statement needed when it is the fixed right factor.
  leavitt-rank-three-support-group-is-virtually-free: that identifies the support subgroup; this applies corner coset projection and the nonunit image to exclude every ambient partner.
  single-conjugated-s3-packet-correction-equation: that adds a kernel packet to the opposite factor; this is the fixed-factor obstruction that kills all such additions at once.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

Let `B=e s~e` be the compression of the explicit rank-three lift of `s_0`.
There is no `C in eF_2[R^x]e` with `CB=e` or `BC=e`.  The support of `B` and
`e` lies in `K_s=(C_2 x C_2)*C_3`, whose group algebra is directly finite.
Corner coset projection would move any ambient one-sided inverse into
`eF_2[K_s]e` and make it two-sided.  Evaluation would then make `s_0` a
unit, contradicting `t_0s_0=1!=s_0t_0`.

