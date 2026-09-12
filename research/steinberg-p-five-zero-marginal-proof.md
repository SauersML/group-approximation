---
rg: 2
id: steinberg-p-five-zero-marginal-proof
kind: route
title: Transport the b=-1 zero plane around the prime-five projective orbit
target: steinberg-zero-plane-transfer-closes-p-five
requires:
  - steinberg-zero-marginal-kills-b-minus-one-plane
  - steinberg-fox-marginal-pushes-are-explicit
---

Assume `P=H=0`.  If `f` vanishes on the plane `b=B`, then its
`r`-difference vanishes there.  Evaluate `Y` on the pre-plane `b=4B`.
The `h^(-1)` term has `b=B`, so the `r`-difference disappears and

```text
Delta_q f(x)=Delta_q f(tau_u x).                       (SPTP1)
```

If `4B!=1`, the map `u` sends this pre-plane birationally to

```text
b=T(B):=4B/(1-4B),                                     (SPTP2)
```

apart from its plane-denominator hyperbola.  On that missing hyperbola,
the pushed point equation `(SBPP4)` has

```text
(A+1/2)C=1+T(B)
```

and evaluates the remaining `q`-difference as

```text
-f(A/[2(1+T(B))], T(B)/[4(1+T(B))],1)
 =-f(A/[2(1+T(B))],B,1)=0.                             (SPTP3)
```

Thus, given the zero plane `B`, the `q`-difference vanishes on `b=4B`
if and only if it vanishes on `b=T(B)`.  On either plane, `(SYZ1)`,
`(SYZ4)`, and `P=0` repeat the last part of the proof of `(SBP1)` and
upgrade `q`-invariance to full vanishing.  If `4B=1`, `u` is
point-exceptional on the entire pre-plane and the same `Y` equation gives
the `q`-difference there directly.

Now work in `F_5`.  Start with `B=-1=4` from `(SBP1)`.  Since `4B=1`,
the exceptional case kills `b=1`.  With `B=1`, the pre-plane `4B=4` is
already zero, so `(SPTP2)` kills

```text
T(1)=4/(1-4)=2.
```

With `B=2`, the post-plane `T(2)=1` is known, so the reverse implication
kills the pre-plane `4B=3`.  Hence every nonzero `b`-plane vanishes.

For `c!=0`, the equation `H(c,ac)=0` now has only one possibly nonzero
summand, namely `x=a`, whose chord has `b=xc-ac=0`.  Therefore
`f(a,0,c)=0`.  Finally the source identity

```text
f(a,b,-1/2)=f(a,b+a/2,0)
```

has a zero left side, and translation in `b` is bijective.  This kills
the `c=0` plane and proves `f=0`.
