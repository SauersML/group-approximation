---
rg: 2
id: kt-canonical-afp-seam-internal-no-go-proof
kind: route
title: Use Fourier coefficients and unique Bass--Serre fixed vertices to exclude an internal seam intertwiner
target: kt-canonical-afp-seam-has-no-internal-gauge-correction
requires:
  - kt-one-compressor-and-sl3-normalizer-lifts-paste
  - kt-finitary-action-is-outer-mod-scalar-core
  - kun-thom-nonsofic-wreath
---

The action of `P_A` on `R` factors through `P_A/N<=G`.  By
`kt-finitary-action-is-outer-mod-scalar-core`, in the `q=2` specialization
every nonidentity element of that quotient acts outerly.  If

```text
x=sum_p x_p u_p in R' cap (R rtimes P_A),
```

then `x_p` intertwines the identity automorphism of the factor `R` with
`alpha_p`.  Outerity forces `x_p=0` for `p notin N`, while for `p in N`
factoriality forces `x_p` to be scalar.  This proves `(KIN2)`.

Suppose a nonzero `z in L(N)` satisfies `(KIN3)` and write its Fourier
coefficients as `(a_n)_(n in N) in l^2(N)`.  Comparing coefficients shows
that this `l^2` function is invariant under the Gamma-action

```text
gamma . n
 =alpha_C(gamma) n (C gamma C^(-1))^(-1).              (KIN4)
```

A nonzero invariant `l^2` function requires a finite orbit.  If `n` has a
finite orbit and `Gamma_0` is its finite-index stabilizer, then

```text
n C Gamma_0 C^(-1) n^(-1)=alpha_C(Gamma_0).             (KIN5)
```

Act on the Bass--Serre tree of `P_A=H_A*_<A>S`.  Every finite-index subgroup
of the infinite Kazhdan group `Gamma` is nonamenable, whereas every edge
stabilizer is conjugate to the cyclic group `<A>`.  Hence `Gamma_0` and
`alpha_C(Gamma_0)` each fix the `H_A` vertex uniquely.  The left side of
`(KIN5)` fixes `nC` times that vertex uniquely.  Equality forces
`nC in H_A`.  But `n in N` maps trivially to `G`, so the quotient map would
put `C` in `H_A`.  This is impossible: the external projection of `H_A` is
`<A>`, while `C notin <A>` (the latter has infinite order and `C` has order
three).  Thus `(KIN4)` has no finite orbit, its only invariant `l^2` function
is zero, and `(KIN3)` has no nonzero solution.
