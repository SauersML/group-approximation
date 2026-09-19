---
rg: 2
id: stw99-xciv-tail-relative-commutants-supply-z-copies
kind: route
title: Build coprime matrix-sum blocks from large Bratteli multiplicities
target: stw99-xciv-norm-matrix-tower-has-zstable-hull
requires: []
---

We first record the integer calculation which drives the proof.  Fix `k>=2`
and put `N=k^2+k+1`.  If `t>=N`, write

```text
t-(2k+1)=ell k+r,       0<=r<k.
```

The lower bound gives `ell>=k-1>=r`, and therefore

```text
t=k(ell-r+1)+(k+1)(r+1).                              (1)
```

Both coefficients in (1) are positive.  Thus every matrix algebra `M_t`
with `t>=N` contains a unital faithful copy of `M_k direct_sum M_(k+1)`:
use `ell-r+1` copies of the first irreducible representation and `r+1`
copies of the second.

Fix `n` and apply (UBT) with this `N`.  In the `j`-th block of `F_m`, the
commutant of the represented `F_n` is

```text
direct_sum_(i:mu_(j,i)>0) M_(mu_(j,i)).
```

By (1), every displayed summand contains a unital faithful copy of
`M_k direct_sum M_(k+1)`.  Taking the same domain diagonally over all
summands and all `j` gives a unital embedding

```text
M_k direct_sum M_(k+1) -> F_n' intersect F_m.          (2)
```

Given a finite subset of `A`, first approximate it in some `F_n`, then use
(2).  The range commutes exactly with `F_n`, so it approximately commutes
with the prescribed finite set.  The standard Blackadar--Kirchberg
formulation of approximate divisibility asks exactly for such approximately
central unital copies of `M_p direct_sum M_q` for arbitrarily large coprime
`p,q`; the pairs `(k,k+1)` therefore suffice.  Thus `A` is approximately
divisible.  Toms--Winter, *Z-stable ASH algebras*, Theorem 2.3 states that
every separable approximately divisible C*-algebra is `Z`-stable, so
`A~=A tensor Z`.  No nuclearity or simplicity hypothesis is added here.

The same argument works inside every tail commutant.  Haar averaging over
the compact unitary group of `F_n` gives a contractive expectation onto
`C_n=F_n' intersect A` and proves

```text
C_n=closure(union_(l>=n) (F_n' intersect F_l)).        (3)
```

Indeed, average any finite-stage approximant to an element of `C_n`; the
average stays at that stage and cannot increase the approximation error.
Given a finite subset of `C_n`, use (3) to approximate it in
`F_n' intersect F_l`.  Apply (UBT) to the inclusion `F_l subset F_m` and the
integer bound above.  The resulting copy of `M_k direct_sum M_(k+1)` lies in

```text
F_l' intersect F_m subset
(F_n' intersect F_l)' intersect (F_n' intersect F_m),
```

so it approximately centralizes the chosen subset of `C_n`.  The same
coprime-matrix-sum criterion makes every `C_n` approximately divisible.
Each `C_n` is separable, so Toms--Winter Theorem 2.3 makes it `Z`-stable.
Composing `z |-> 1 tensor z` with a `Z`-absorption isomorphism supplies a
unital homomorphism `Z->C_n`.

Now let finite `E subset S`, finite `G subset Z`, and `epsilon>0` be given.
Set `M=max(1,max_(z in G)||z||)`.  Choose `n` so that every `x in E` has
some `b_x in F_n` with

```text
||x-b_x|| < epsilon/(2M).
```

Choose a unital `phi:Z->C_n`.  Since `phi` is isometric and
commutes with `b_x`,

```text
||[x,phi(z)]||
 <= 2 ||x-b_x|| ||phi(z)||
 < epsilon
```

for `x in E` and `z in G`.  All estimates are in operator norm.  Hyperfinite
`2`-norm approximation of arbitrary elements of `R` supplies none of the
displayed distance hypothesis, so the argument does not extend to all of
`R` and does not resolve the XCIV root.
