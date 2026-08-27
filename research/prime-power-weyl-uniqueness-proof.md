---
rg: 2
id: prime-power-weyl-uniqueness-proof
kind: route
title: Solve the projective normalizer equations over the local ring
target: prime-power-iwahori-weyl-endpoint-is-unique-away-from-three
requires: []
---

Put `A=Z/p^k Z` and lift `x` to

```text
X=[a b;c d] in SL_2(A).
```

The projective inversion equation says

```text
X h(2) X^(-1)=epsilon h(2^(-1)),       epsilon in {+1,-1}.   (PPW1)
```

First take `epsilon=+1`.  Comparing the four entries of
`Xh(2)=h(2^(-1))X` gives

```text
(3/2)a=0,       (3/2)d=0.                              (PPW2)
```

Since `p>3`, `3/2` is a unit, so `a=d=0`.  The determinant condition gives
`-bc=1`, and therefore

```text
X=h(q)w=[0 -q;q^(-1) 0]                               (PPW3)
```

for one unit `q`.

There is only one possible extra projective lift.  If `epsilon=-1`, entry
comparison gives

```text
b=c=0,       (5/2)a=(5/2)d=0.                         (PPW4)
```

For `p!=5` this contradicts `det X=1`.  For `p=5,k>=2`, both `a,d` lie in
the annihilator of `5`, hence are divisible by `5^(k-1)` and again cannot
have product one.  For `p=5,k=1`, `(PPW4)` permits a diagonal lift
`X=h(q)`; this exceptional field branch will be excluded by the cubic below.

For the Weyl branch `(PPW3)`, put `M=Xt`.  It has determinant one, unit
off-diagonal entry, and trace `z=q^(-1)`.  Cayley--Hamilton gives

```text
M^3=(z^2-1)M-zI.                                      (PPW5)
```

The projective cubic says `M^3=delta I` for `delta=+-1`.  Looking at the
unit off-diagonal entry in `(PPW5)` forces `z^2=1`.  Over the odd local
ring `A`, the only roots of `z^2=1` are `+-1`; hence `q=+-1`.  The two
lifts differ by `-I` and define the same projective element `w`.

It remains to eliminate the diagonal branch at `p=5,k=1`.  There
`M=h(q)t` has unit off-diagonal entry and trace `z=q+q^(-1)`, so the same
argument forces `z^2=1`.  For the four units of `F_5`, the values of `z`
are `2,-2,0,0`, none of whose squares is one.  Thus the branch is empty,
and `w` is unique in all cases.

