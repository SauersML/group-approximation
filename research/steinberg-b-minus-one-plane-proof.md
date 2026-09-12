---
rg: 2
id: steinberg-b-minus-one-plane-proof
kind: route
title: Push Y through the plane marginal and close the projective C-orbit
target: steinberg-zero-marginal-kills-b-minus-one-plane
requires:
  - steinberg-x-row-splits-zero-marginal-tree-sectors
  - steinberg-y-propagates-matching-to-zero-families
  - steinberg-fox-marginal-pushes-are-explicit
---

Put `g=(1-q)f`.  Under `P=H=0`, `(SMP3)` gives `P_g=H_g=0`, and all
one-dimensional marginals vanish as well.  Push

```text
Yf = g-L_u g-L_(h^(-1)r)f+L_(h^(-1))f=0
```

through `H`.  The first and last terms have zero plane marginal.  Formula
`(SMP2)` shows that `H_(L_r f)=0`, including its exceptional branch,
because `H=A=0`.  Scaling by `h^(-1)` preserves this conclusion.  Hence

```text
H_(L_u g)=0.                                             (SBPP1)
```

Use the generic branch of `(SMP5)`.  In its original plane variables put

```text
E=1+d+c/2,   A=-(2+c)/(2c),   C=c/E,
D=d/E,       B=AC-D.
```

For `c!=0` and `E!=0`, one has

```text
1/c=-(A+1/2),
D=1-C/c-C/2,
B=AC-1+C/c+C/2=-1.
```

Conversely every `A!=-1/2`, `C!=0` occurs.  Therefore `(SBPP1)` and
`(SMP5)` give

```text
g(A,-1,C)=0            (A!=-1/2, C!=0).                (SBPP2)
```

The first source identity `(SXTS2)` supplies `(SBPP2)` at `A=-1/2`.
Moreover

```text
sum_C g(A,-1,C)=P(A,-1)-P(A+1/2,-1)=0,
```

so the only missing value `C=0` is zero as well.  Thus
`f(A,-1,C)=k_C` is independent of `A`.

Now `(SYZ1)` says `k_(-1)=0`.  Taking `B=-1` in `(SYZ4)` gives

```text
k_t=k_(t/(1+t))                    for t!=-1.           (SBPP3)
```

For every `t!=0`, iteration reaches `-1`: one may take
`n=-t^(-1)-1` in `phi^n(t)=t/(1+nt)`.  Hence `k_t=0` for all `t!=0`,
and `P(A,-1)=sum_C k_C=0` gives `k_0=0`.  This proves `(SBP1)`.

For the first identity in `(SBP2)`, push `Y` through `P`.  The scaled
`h^(-1)` terms and `(SMP4)` give

```text
0=P_Y(a,b)=-P_(L_u g)(a,b)+f(a/2+b/4,b/4,1).           (SBPP4)
```

At `b=1`, `(SMP4)` gives `P_(L_u g)(a,1)=0`: generically it is a value
of `H_g`, and at `a=-1/2` it is `-A_g(-1/2)`.  Since
`a/2+1/4` runs through `F_p`, `(SBPP4)` proves `f(A,1/4,1)=0`.

Finally evaluate `Xf=A(1-q)f+B(1-s)f-f` at
`x=(a,2a-1,1)`.  For `a!=1/2`, the `A`-image is

```text
(a/(1-2a),-1,2a-1),
```

so its `q`-difference vanishes by `(SBP1)`; at `a=1/2` it is the zero
tree coefficient.  Since `c=1`, the `B(1-s)` term is also a zero tree
coefficient.  Thus `f(a,2a-1,1)=0`.
