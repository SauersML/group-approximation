---
rg: 2
id: atlas-mixed-c3-gram-has-local-zero-interval
kind: claim
title: The gauge-invariant mixed C3 Gram leakage has a collision-zero interval on the regular local profile
artifacts:
  - experiments/atlas_a4_common_u_theta_slice.py
  - research/artifacts/atlas-a4-common-u-theta-slice-2026-08-21.json
distinct_from:
  atlas-common-u-c3-compression-is-two-covariance-residuals: that expands the leakage as an exact sum of squares; this places it on the twelve-double-coset quotient and computes its collision-zero local range.
  atlas-19243-common-u-regular-local-hub-gram-escape: that varies the hub first and second moments; this varies the cross-component C3 compression which survived the rectangle-gauge audit.
  atlas-a4-19243-type-relaxation-has-regular-zero: that gives one zero-collision type point after forgetting operators; this shows the first gauge-invariant mixed operator coordinate is still not fixed on that point.
---

Let

```text
P=P_6,
C(U)=U^*rho(b_0)U,
Z(U)=E_K^- C(U) E_K^+,
Lambda(U)=||Z(U)-PZ(U)P||_2^2.                         (MCG1)
```

On the twelve-double-coset system choose any edge and write

```text
U=X_e R Y_e.                                           (MCG2)
```

Then `(MCG1)` with `(MCG2)` is independent of the edge and invariant under
all twelve gauges

```text
(X_e,Y_e)->(X_eW_e,W_e^(-1)Y_e),                      (MCG3)
```

because every gauge leaves the product `X_eRY_e` fixed.  Thus `Lambda` is the
first mixed projection-Gram coordinate from the preceding rectangle audit
which genuinely descends to the common-frame quotient.

For every unitary `U`,

```text
0<=Lambda(U)<=||Z(U)||_2^2<=min(tau(E_K^+),tau(E_K^-))=1/6. (MCG4)
```

The lower endpoint cannot be replaced by a positive constant using collision
19243 and the exact regular finite-subgroup profiles.  In the established
six-dimensional collision family, with reflection angle `theta`,

```text
q_19243(U_theta)=1,
rho|_K=Reg(S3),
rank_+(c_theta)=rank_-(c_theta)=3,
Z(U_theta)=sin(2theta) Z_*,
||Z_*||_2^2=1/6.                                      (MCG5)
```

The standard blocks have `c=+I` and `c=-I`, so only the single
`triv-to-sign` matrix entry contributes to `(MCG5)`; normalized trace on the
six-dimensional cell gives `1/6`.  Amplifying by `3360k` embeds the same
family at the regular `A8` restriction scale without changing normalized
norms.

Consequently

```text
Lambda(U_theta)=sin(2theta)^2 Lambda_*,                (MCG6)
Lambda_*:=||Z_*-PZ_*P||_2^2.
```

The exact two-carrier angle theorem gives

```text
((9-sqrt(17))/18)(1/6)<=Lambda_*<=1/6.                (MCG7)
```

Therefore the collision-zero, exact-regular **profile-relaxed** feasible set
of the mixed invariant contains the entire nondegenerate interval

```text
[0,Lambda_*],                                         (MCG8)
```

including the explicit zero escape `theta=0`.  Collision and regular edge
profiles do not even determine the first surviving gauge-invariant Gram
coordinate.

This does not construct a zero escape in the full twelve-double-coset matrix
system: the local family is not known to satisfy the other packet component's
twelve common-product equations.  On the full system, the feasible sets

```text
I_k={Lambda(X_eRY_e): (CUL3) holds at multiplicity k}  (MCG9)
```

are compact semialgebraic subsets of `[0,1/6]` and satisfy
`I_k subseteq I_(lk)` under amplification.  Proving the desired exact
common-frame compression is precisely proving `I_k subseteq {0}` for every
`k`; a positive element of any `I_k` is an exact matrix counterexample.  The
interval `(MCG8)` proves that such a conclusion must use the full simultaneous
double-coset lift, not collision or representation profiles.

## Bounded `k=1` canonical-lift probe

The accompanying implicit regular-`A8` experiment starts from one reproducible
lift of the local family without materializing a `20160`-square matrix.  It
pairs the two regular involution matchings cyclewise relative to the fixed
packet alignment and repeats the six-dimensional line rotation over the
`3360` left-`K` cosets.  Before the centralizer optimization, that lift has the
exact formula

```text
||U_theta-U_0||_2^2=(2/3)(1-cos(theta)),               (MCG10)
```

and satisfies collision 19243 identically.  The current experiment enlarges
this to the repeated `U(3) x U(3)` centralizer subfiber and chooses its exact
nearest-reference Procrustes point.  Twelve fixed Rademacher probes gave
packet RMS defects `1.3906, 1.3912, 1.3972, 1.4044` at
`theta=0,0.1,0.4,pi/4`, respectively.  Thus that optimized repeated-block
slice is still far from the packet locus and supplies no positive-`Lambda`
candidate.

This is deliberately only numerical evidence about one section of the
conjugator fiber.  The collision family fixes `U^*rho(b_0)U`, not `U`; the
large commutant of `rho(b_0)` leaves many other lifts.  Therefore the probe is
neither a lower bound for `(CUL3)` nor evidence that `I_1 subseteq {0}`.

`atlas-repeated-collision-fiber-is-two-block-procrustes` now enlarges that
single section to the block-repeated `U(3) x U(3)` collision subfiber and
solves its nearest-reference projection exactly by two `3 x 3` polar
decompositions.  The optimized slice remains numerically far from the packet,
but the unrestricted `U(10080) x U(10080)` conjugator fiber is untouched.
