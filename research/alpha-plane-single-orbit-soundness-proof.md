---
rg: 2
id: alpha-plane-single-orbit-soundness-proof
kind: route
title: Apply affine single-orbit soundness to the primitive alpha-plane constraint
target: phased-translations-reduce-to-alpha-plane-test
requires:
  - two-untwisted-field-matchings-force-complete-cross-commutation
---

For `P:K->F_2`, the sampled constraint is

```text
P(x)+P(x+b)+P(x+alpha b)+P(x+(1+alpha)b)=0.                  (AP1)
```

These are exactly the images of the one four-point constraint on
`{0,1,alpha,1+alpha}` under all affine maps `t |-> x+bt` of the
one-dimensional `K`-space.  The four locations are the `K`-linear forms

```text
x,             x+b,             x+alpha b,             x+(1+alpha)b.
                                                                    (AP2)
```

They are pairwise independent as forms in `(x,b)`.  In particular `(AP1)` is
a 2-ary-independent four-local formal characterization in the terminology of
Kaufman--Sudan.

It remains only to identify its kernel.  If `(AP1)` holds for every `x,b`,
then the phased translations `(PT1)` satisfy both exact primitive matchings.
`two-untwisted-field-matchings-force-complete-cross-commutation` therefore
gives `Delta_a Delta_b P=0` for all `a,b`.  Hence `P` is affine over `F_2`.
Conversely every affine Boolean function plainly satisfies `(AP1)`.  Thus the
orbit in `(AP1)` characterizes exactly the first-order Reed--Muller code on
the additive `F_2`-space of `K`.

Theorem 2.9 of [Kaufman--Sudan, *Algebraic Property Testing: The Role of
Invariance*](https://people.csail.mit.edu/madhu/papers/2007/apt-full.pdf)
applies directly to this already-formal characterization.  For a
2-ary-independent `k`-local formal characterization it states that rejection
is at least

```text
min{rho/2, 1/((2k+1)(k-1))},                                (AP3)
```

where `rho` is relative Hamming distance from the property.  With `k=4`,

```text
r_alpha(P) >= min{rho(P,RM(1))/2, 1/27}.                    (AP4)
```

This constant is independent of `|K|=2^n`.

Choose an affine `L` at distance `rho` from `P`.  Since the complete
parallelogram parity of `L` vanishes, a union bound over its four vertices
gives

```text
r_all(P) <= 4 rho.                                           (AP5)
```

Also, with `F=(-1)^P` and normalized Fourier coefficients,

```text
1-2 r_all(P)=sum_chi Fhat(chi)^4 >=0,                        (AP6)
```

so `r_all(P)<=1/2`.  If `r_alpha<1/27`, `(AP4)` and `(AP5)` give
`r_all<=8 r_alpha`.  If `r_alpha>=1/27`, `(AP6)` gives
`r_all<=1/2<=(27/2)r_alpha`.  This proves `(PT5)` and `(PT6)`.
