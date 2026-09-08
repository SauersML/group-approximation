---
rg: 2
id: leavitt-four-word-packet-has-an-exact-24-dimensional-model
kind: claim
title: All four Leavitt packet words vanish in an explicit frozen 24-dimensional permutation model
distinct_from:
  leavitt-first-relation-has-a-4608-dimensional-seed: that supplies an exact first-relation model which fails two further coefficient words; this satisfies all four current packet words already at dimension 24.
  leavitt-kernel-packet-has-a-finite-coefficient-rank-gap: that excludes literal characteristic-two coefficient matrices; this uses a finite abstract group whose derived constant-root word has order three, outside that coefficient realization.
  leavitt-24k-feasibility-vanishes: that asks for vanishing on every finite stage of the full kernel exhaustion; this solves only the displayed four-word packet and explicitly fails another true kernel word.
artifacts:
  - research/artifacts/leavitt-four-word-packet-24-point-countermodel-2026-09-08.md
---

On the frozen basis `|a,x>`, with `a in Z/3` and `x in F_2^3`,
set

```text
U|a,x>=|(-1)^(x_1+x_2+x_3)a,x>.
```

This is a permutation involution. In zero-based indices `8a+x`,
with `x=x_1+2x_2+4x_3`, it is

```text
U=(9 17)(10 18)(12 20)(15 23).
```

Then the frozen relative-unitary representation at `k=1` satisfies
all four words `r_*`, `R_v`, `R_0`, and `R_sum` of
`leavitt-24k-kernel-packet-excludes-scalar-field-models` exactly.
Its image is the regular permutation representation of
`S_3 x C_2^2`, and both marked factors embed. Amplifying by `I_k`
gives an exact solution in every dimension `24k`. Thus the minimum
of the maximum of these four defects is zero for every `k`, in
both normalized-HS and operator norm.

The native relation `d^2=1`, where `d=[b_2,c b_1 c^(-1)]`,
fails: here `pi(d)=C_k^2` and `pi(d^2)=C_k`, at normalized-HS
distance `sqrt(2)` from the identity. In the actual Leavitt group
`d=x_13(1)` is an involution. Adding this missing relation excludes
the displayed model but is not asserted to exclude every model.
Neither the enlarged packet nor the full relation exhaustion is
decided here.

DERIVATION
leavitt-packet-s3-central-padding-countermodel
