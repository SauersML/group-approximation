---
rg: 2
id: steinberg-weighted-transform-firewall-proof
kind: route
title: Pull arbitrary weights through u and identify the generated SL2 module
target: steinberg-nonconstant-weights-generate-full-projective-module
requires:
  - steinberg-fox-marginal-pushes-are-explicit
---

Let `g=(1-L_q)f` and write

```text
W_w^P Q(a)=sum_b w(b)Q(a,b),
W_w^H Q(c)=sum_d w(d)Q(c,d).
```

Reparametrize `(SMP4)` by `t=b/(1-b)`.  For `a!=-1/2`,

```text
W_w^P(L_u g)(a)
=-sum_(t!=-1) w(t/(1+t))
       g(a+(a+1/2)t,t,(a+1/2)^(-1))
 +w(1)H_g((a+1/2)^(-1),a/(a+1/2)).                   (SWTF3)
```

At `a=-1/2`, the same calculation gives

```text
sum_(t!=-1)w(t/(1+t))P_g(-1/2,t)-w(1)A_g(-1/2).
```

On the plane side, for `c!=0`, put
`a_*=-(2+c)/(2c)` and `d_0=-1-c/2`.  Reparametrizing by
`z=c/(1+d+c/2)` gives

```text
W_w^H(L_u g)(c)
=w(d_0)g(a_*,-1,0)
 +sum_(z!=0)[w(d_0)-w(d_0+c/z)]g(a_*,-1,z),           (SWTF4)
```

and the value is zero at `c=0`.  Thus the pushed weights contain affine
translations and the Möbius map in `(SWTF1)`; these are the two root
subgroups generating `SL_2(F_p)`.

Because `p+1=1` in `F_p`, the constant vector is not in the augmentation
subspace, giving the direct sum `(SWTF2)`.  The augmentation permutation
module is the rank-one Steinberg module and is simple.  Any nonconstant
weight has a nonzero augmentation component; its orbit therefore spans
`St_2`, and adding the constant equation spans all `p+1` point masses.
Weighted marginal equations for all point masses are exactly the original
pointwise slice system, proving the scoped firewall.
