---
rg: 2
id: sl3-double-one-vertex-anchor-proof
kind: route
title: Project the relative h-error to the co-dense commutant and kill it by Bezout exponent sums
target: sl3-double-one-near-vertex-forces-joint-near-exactness
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Choose a finite relative presentation

```text
A=<C,h | R>.
```

Such a presentation exists because `A` and `C` are finitely presented and
`A=<C,h>`.  Put `B=C cap h^(-1) C h`.  This is finite index in `C`, hence
has property (T).  Moreover every finite-dimensional unitary representation
`alpha` of `A` satisfies

```text
alpha(B)=alpha(C)=alpha(A).                               (OVA2)
```

Indeed `alpha` factors through an odd congruence quotient.  The subgroup
`B` contains a principal 2-power congruence subgroup of `C`; Chinese
remaindering and congruence surjectivity show that `B` surjects onto every
odd congruence quotient.  This proves `(OVA2)`.

The amalgamating relators and the near-exactness of `pi_0` give
`pi_1(c)=alpha(c)+o_HS(1)` on a fixed generating set of `C`.  Write

```text
H=alpha(h),   U=pi_1(h),   u=H^*U.
```

For `b` in a fixed Kazhdan set of `B`, the relative relation
`h b h^(-1) in C` gives

```text
||[u,alpha(b)]||_2 <= O(delta+epsilon).                   (OVA3)
```

Property (T) for `B`, applied to `Ad alpha` on Hilbert--Schmidt matrices,
projects `u` within `O(delta+epsilon)` of `alpha(B)'`.  Polar decomposition
inside that finite-dimensional commutant gives a unitary

```text
v in alpha(B)'=alpha(A)',   ||u-v||_2<=O(delta+epsilon).   (OVA4)
```

Define the comparison tuple by `beta(c)=alpha(c)` and
`beta(h)=alpha(h)v`.  Since `v` commutes with `alpha(A)`, every relative
relator `r in R` evaluates on `beta` as

```text
r(beta)=v^(e_r),                                          (OVA5)
```

where `e_r` is the total `h`-exponent of `r`.  Fixed-word telescoping from
`pi_1` and `(OVA4)` makes every `v^(e_r)` close to one.

Finally

```text
gcd{e_r:r in R}=1.                                       (OVA6)
```

Indeed, after normally killing `C`, the presentation becomes the cyclic
presentation `<h | h^(e_r), r in R>`.  Its group is `A/<<C>>`.  But `A` is
perfect and the quotient is cyclic, hence trivial.  Thus `(OVA6)` holds.
Fix Bezout coefficients `a_r` with `sum a_r e_r=1`.  Since all powers of
the single unitary `v` commute,

```text
||v-I||_2
 <= sum_(r in R)|a_r| ||v^(e_r)-I||_2
 <= O(delta+epsilon).                                    (OVA7)
```

Equations `(OVA4)` and `(OVA7)` give `U=H+o_HS(1)`; the amalgam already
gave the same conclusion on `C`.  Fixed generator-word telescoping proves
`(OVA1)`.  Every constant depends only on the fixed relative presentation,
the Kazhdan pair of `B`, and the chosen Tietze translations, never on `d`.

