---
rg: 2
id: atlas-equal-block-flattening-is-commutant-gauge
kind: claim
title: Stable equal-block flattening is a regular-chart commutant gauge
invalidates:
  - atlas-equal-block-biunitary-witness
distinct_from:
  atlas-stabilizer-commutant-no-go: that excludes one stabilizer-commutant deformation by an extra exact cross-chart relation; this shows that equal operator-block norms can be installed by a full-chart commutant gauge without changing any represented word.
  atlas-full-relator-data-factor-through-double-commutant-gauge: that identifies the intrinsic double-coset gauge of the relator objective; this gives an explicit finite stabilization which flattens all block Hilbert--Schmidt norms inside one such gauge orbit.
  atlas-true-criterion-baseline: that evaluates the tensor flip; this constructs a maximally flat magic-block representative of exactly the same tensor-flip representation.
---

**ESTABLISHED FLATNESS FIREWALL.**  Let `A` be a finite group of order `m`,
let `L,R` be its commuting left and right regular representations on
`H=l2(A)`, and let

```text
U in U(H tensor C^k)
```

be any relative unitary between two regular `A` charts.  After the fixed
`m`-fold stabilization there is a relative unitary

```text
U_hat in U(H tensor C^k tensor l2(A))
```

such that:

1. every `H`-matrix block of `U_hat` has the same Hilbert--Schmidt norm;
2. the second chart represented by `U_hat` is exactly the amplification of
   the second chart represented by `U`; and consequently
3. every free-product word has exactly the same normalized trace and
   normalized-Hilbert--Schmidt defect before and after flattening.

The construction is an explicit commutant gauge.  If `p_a` is the rank-one
projection onto `delta_a` in the new multiplicity copy, put

```text
C=sum_(a in A) R_a tensor I_k tensor p_a,
U_hat=(U tensor I_m) C.                                  (EBF1)
```

Then `C` is unitary and commutes with the first chart.  Relative to the
`H` coordinate its `(z,y)` block is `I_k tensor p_(alpha(z,y))`, where
`alpha(z,y)` is the unique group element carrying `delta_y` to `delta_z`
under the chosen right-regular convention.  Therefore

```text
(U_hat)_(x,y)=sum_z U_(x,z) tensor p_(alpha(z,y)),        (EBF2)
```

and the summands are Hilbert--Schmidt orthogonal.  Row unitarity of `U`
gives

```text
||(U_hat)_(x,y)||_HS^2
 =sum_z ||U_(x,z)||_HS^2
 =k,                                                     (EBF3)
```

independent of both `x` and `y`.  Equivalently, every block has normalized
block `2`-norm squared `1/m`.

At the tensor flip `J`, the blocks of `(J tensor I_m)C` are precisely the
rank-one projections `p_(alpha'(x,y))`.  Each block row and block column is
an orthogonal projection-valued partition of the multiplicity identity, so
this is a magic/quantum-Latin operator-block unitary with perfectly equal
block norms.  Nevertheless its second chart is still the right regular
chart:

```text
Ad((J tensor I_m)C)(L_g tensor I_m)=R_(sigma(g)) tensor I_m.  (EBF4)
```

Hence the two charts commute completely.  In the Atlas criterion all
cartesian control words still vanish, while every single-factor cartesian
escapee has exactly the tensor-flip defect `sqrt(2)`.

Thus stable equal-block norm, even in the maximally flat magic-block example,
is not evidence of noncommuting Atlas holonomy.  The property is not
gauge-invariant.  Any positive operator-valued-Hadamard or quantum-Latin
construction must separately prove a gauge-invariant escape condition, such
as positive cross-chart commutator energy or decay of a named cartesian
escapee; flat block geometry alone supplies none.

DERIVATION
atlas-equal-block-flattening-commutant-gauge-proof
