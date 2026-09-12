---
rg: 2
id: corner-renormalization-cost
kind: claim
title: Corner compression is free in operator norm and costs the inverse root trace
distinct_from:
  trace-blindness-sharpness: That claim says no conjugation-invariant monotone size exists in a II_1 factor; this one is a quantitative comparison of what compression does to operator-norm and to normalized Hilbert--Schmidt data.
artifacts:
  - notes/FALSE_FERMIONIC_AMPLIFICATION.md
  - notes/FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md
---

Let `A` be unital with tracial state `tau`, let `p != 0` be a projection with
`tau(p)>0`, and equip `pAp` with the renormalized trace
`tau_p = tau(p . p)/tau(p)`.  Then for all `x in A`

```text
||pxp||_op <= ||x||_op,                                          (C1)
||pxp||_(2,tau_p) <= tau(p)^(-1/2) ||x||_(2,tau),                (C2)
```

and `(C2)` is attained whenever `x=pxp`.  Thus operator-norm data is
corner-stable at zero cost, while tracial data pays exactly
`tau(p)^(-1/2)`, unbounded precisely when the corner is trace-null.

The cost is the *normalization*, not the norm.  In matrices, for a rank-`r`
corner and `||A||_op <= 2`,

```text
||A||_(2,r)^2 = Tr(A^*A)/r <= 2 Tr(|A|)/r <= 2 ||A||_1,          (C3)
```

so an **unnormalized** Schatten-one (or Frobenius) hypothesis converts into a
normalized Hilbert--Schmidt conclusion in the corner with no density loss
whatever, however small `r/d` is.  That is the whole mechanism of
`schatten-one-corner-detector`, and the reason no analogous statement holds
for a normalized Schatten-one or normalized Hilbert--Schmidt hypothesis,
where the entire error may concentrate on the selected `o(d)` corner.

For `p` of rank `r` in `M_d` the cost is `sqrt(d/r)`.  This is the same
constant as the two other known bottlenecks of the norm-to-trace passage:
the functorially optimal amplification loss
`Lip_2(R) >= (sqrt(floor(d/r))/pi) Delta_(R,r)` of
`FALSE_FERMIONIC_AMPLIFICATION.md`, Theorem 5, and the effective-rank
profile `epsilon_n sqrt(d_n/r_eff)` of
`FALSE_WEAK_MF_EFFECTIVE_RANK_PROFILE.md`.  Compression, amplification, and
rank spreading are three descriptions of one constant.
