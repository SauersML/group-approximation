---
rg: 2
id: finite-image-summit-wreath-relative-h1-vanishes
kind: claim
title: Every finite-image summit-wreath representation has zero relative first cohomology
distinct_from:
  finite-wreath-relative-tangent-moduli-vanish: that averages cocycles after replacing the whole source by a finite wreath packet; this treats the actual infinite summit wreath and proves that moving finite-quotient kernel words contribute no real tangent directions.
  wreath-ball-area-controls-only-true-group-cells: that shows presentation defect does not control moving quotient-kernel cells; this computes their exact infinitesimal deformation space and finds it zero.
  coset-wreath-microstates-carry-excess-entropy: that asks for nonlinear approximate moduli at positive scale; this rules out every local finite-image/congruence-kernel tangent source for those moduli.
---

Let

```text
W_3=(direct_sum_(Gamma/Lambda) C_2) rtimes Gamma,
Gamma=SL_3(Z[1/3]),       Lambda=SL_3(Z),               (FIR1)
```

and let `rho:W_3->U(d)` have finite image `H`.  Put `N=ker rho` and
`M=u(d)` with the adjoint `W_3`-action.  Then

```text
H^1(W_3,M)=0.                                           (FIR2)
```

In particular every linearized deformation of `rho` is a global-conjugacy
tangent.  If the deformation vanishes on the actor subgroup `Gamma`, its
primitive lies in `rho(Gamma)'`, so the relative lamp-over-base tangent
quotient also vanishes.

The key point is that the moving quotient kernel has torsion abelianization.
Let `A=direct_sum C_2`, put `B=N cap A`, and let `Gamma_N` be the projection
of `N` to `Gamma`.  Since `N` has finite index in `W_3`, `Gamma_N` has finite
index in `Gamma`, and

```text
1 -> B -> N -> Gamma_N -> 1.                            (FIR3)
```

The group `B` has exponent two.  The `S`-arithmetic group `Gamma` has
property `(T)`, as does its finite-index subgroup `Gamma_N`; since it is
finitely generated, `Gamma_N^ab` is finite.  Abelianizing `(FIR3)` shows that
the kernel of `N^ab->Gamma_N^ab` is a quotient of `B`, hence has exponent
two.  Therefore

```text
N^ab is torsion,
Hom(N^ab,M)=0.                                          (FIR4)
```

Because `N` acts trivially on `M`, inflation--restriction gives

```text
0 -> H^1(H,M) -> H^1(W_3,M)
  -> Hom(N^ab,M)^H -> H^2(H,M).                        (FIR5)
```

Both outer finite-group cohomology terms vanish over the real vector space
`M` by averaging, while the middle target vanishes by `(FIR4)`.  This proves
`(FIR2)`.

Thus the number of independent real moving-kernel tangent directions is
exactly zero before any entropy normalization; after quotient by global (or
actor-fixing) conjugacy it remains zero.  The uncontrolled quotient-kernel
cells isolated by `wreath-ball-area-controls-only-true-group-cells` can only
support an entropy witness through genuinely nonlinear approximate models
which remain away from every finite-image representation.  They cannot be
activated by infinitesimally perturbing congruence/multiplicity enemies.

This theorem is exact, not a uniform stability statement.  The averaging and
inflation--restriction argument supplies no presentation-level modulus when
the finite quotient and its kernel generators move with `d`.  That missing
uniformity is now the sole way finite-quotient neighborhoods could still
contribute to the entropy seam.

The analytic boundary is sharpened by
`bernoulli-adjoint-gauges-fence-uniform-wreath-newton`: pointwise `H^1=0`
does not provide a uniform transverse singular value or a global capture
radius, and the Bernoulli lamp deformation explicitly kills any attempt to
deduce a uniform all-representation adjoint gauge gap from the property-`(T)`
actor and the Cartan alone.
