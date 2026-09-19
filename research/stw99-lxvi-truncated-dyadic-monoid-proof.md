---
rg: 2
id: stw99-lxvi-truncated-dyadic-monoid-proof
kind: route
title: Saturate dyadic addition at one and compute the exact fullness thresholds
target: stw99-lxvi-truncated-dyadic-monoid-has-finite-halving-seed
requires: []
artifacts:
  - research/artifacts/stw99-lxxiii-lxvi-focused-audit-2026-08-31.md
---

The operation in (TDM1) is associative because both parenthesizations of a
three-term sum equal `min(1,r+s+t)`.  It is commutative, has identity zero,
and is conical because a saturated sum is zero only when both summands are
zero.

If an order ideal contains `0<r in M`, choose `k` with `kr>=1`.  Its
`k`-fold monoid sum is `u=1`.  Every `s in M` satisfies `s<=u` in the
algebraic order, since `s plus_M u=u`; heredity then puts every `s` in the
ideal.  Hence `M` is simple.

The identities `u plus_M u=u` and

```text
p plus_M y=p  ==>  min(1,1/2+y)=1/2  ==>  y=0
```

give proper infiniteness of `u` and finiteness of `p`.  Ordinary addition
does not saturate below one, so `2x_(n+1)=x_n` and every `x_n<1` is finite.

Finally, `m x_n<1` exactly when `m<2^(n+1)`.  Therefore the first multiple
which reaches `u` is `m_n=2^(n+1)`.  Since `u` is not below a proper element
`x_n` in the algebraic order, all assertions in (TDM3) follow.
