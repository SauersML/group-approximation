---
rg: 2
id: endpoint-triangle-charges-bs-sign-cut-volume
kind: claim
title: An authenticated endpoint triangle charges the full volume of every BS spectral sign cut
distinct_from:
  bs-core-coarea-cuts-have-full-legalization-cost: that shows a half-interval has constant BS-core boundary but linear exact-core legalization cost; this proves the endpoint involution and first cubic already charge that linear volume.
  sign-plateau-involution-split-or-pay: that rounds a general approximate sign plateau without an exact same-core endpoint; this gives a sharp direct estimate relative to one authenticated exact endpoint.
  same-core-involution-cubic-gauge-coercivity: that proves the general relative-gauge inequality; this specializes it to hard spectral cuts and computes the resulting rank and cyclic-boundary ledger.
---

Let `(X_0,R,S)` be an exact Iwahori endpoint and put `T=S^2`.  For any
spectral projection `P` of `S`, let

```text
D=1-2P,                       X=D X_0.                (ETC1)
```

Then `D` commutes with `T`, and the exact finite-difference identity gives

```text
||D-1||_F
 <=||X^2-1||_F+||(XT)^3-1||_F.                       (ETC2)
```

Consequently

```text
||X^2-1||_F^2+||(XS^2)^3-1||_F^2
 >=(1/2)||D-1||_F^2=2 rank(P).                       (ETC3)
```

The second cubic and inversion rows are nonnegative additions, so the full
endpoint energy has the same lower bound.  If the hard cut is compatible
with the reflection row, meaning `X^2=1`, then the first cubic alone obeys

```text
||(XS^2)^3-1||_F^2>=4 rank(P).                       (ETC4)
```

Apply this to the length-`m` packet and half-interval projection in
`bs-core-coarea-cuts-have-full-legalization-cost`.  Although its exact
BS-core boundary satisfies `||[P,R]||_F^2=2`, every compatible reflection
modification has first-cubic energy at least `4 floor(m/2)`, and without
compatibility the square-plus-cubic energy is at least `2 floor(m/2)`.
Thus the proposed interval counterpacket is impossible after an exact
same-core endpoint has been authenticated.

More generally, if `P_A` is the diagonal projection of any subset
`A subset Z/m` in a scalar cycle packet, then

```text
||[1-2P_A,R]||_F^2=4 |A triangle (A+1)|,             (ETC5)
```

while `(ETC3)` charges `2|A|`.  Hence endpoint rows convert the cyclic
boundary ledger into a volume ledger uniformly over arbitrary unions of
intervals.  This closes the hard-cut/coarea test **inside an authenticated
same-core endpoint basin**.  It does not select `X_0` from the raw tuple;
using `(ETC2)` before that selection would assume the remaining part of
`(GOS1)`.

