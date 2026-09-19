---
rg: 2
id: finite-index-induction-coefficient-residual-proof
kind: route
title: Induce packet-bearing high Kazhdan types across the finite covariance orbit
target: finite-index-covariance-retains-coefficient-residual
requires:
  - high-type-irreducibles-retain-finite-packet-mass
  - kazhdan-bounded-types-form-central-summand
  - one-bounded-type-coefficient-separates-unbounded-exits
---

Extract irreducibles `pi_j` of `Lambda` with degree tending to infinity and
`tr(pi_j(z))>=q/2`.  For any inclusion `Lambda<G` of finite index `m`, form
`rho_j=Ind_Lambda^G(pi_j)`.  The identity-coset fiber is reducing for
`rho_j(Lambda)` and carries `pi_j`.  Once `dim(pi_j)>K`, that fiber kills the
bounded-type central projection `p_<=K`.

The identity fiber supplies packet trace at least `q/2`; the complementary
trace is nonnegative because `z` is a projection.  Normalized over the `m`
fibers this gives

```text
tr(rho_j(z))>=q/(2m).
```

If `||a-p_<=K||_max<=epsilon<1`, then `||pi_j(a)||_op<=epsilon` on that
fiber.  Its contribution to the whole normalized Hilbert--Schmidt norm gives

```text
||rho_j(z)(1-rho_j(a))||_2
 >=m^(-1/2)||pi_j(z)(1-pi_j(a))||_2
 >=m^(-1/2)(1-epsilon)||pi_j(z)||_2
 >=(1-epsilon)sqrt(q/(2m)).
```

Every ordinary relator of the overgroup is nevertheless exact in `rho_j`.
Thus no finite-index overgroup can bound this coefficient residual by
ordinary relator energy.  Crossed products by finite automorphism groups,
and their finite-order projective variants after a fixed finite central
extension, are special cases, so the argument closes those coefficient
compilers at once.  When `Lambda` is normal, the full restriction is a sum
of high-dimensional conjugates and `rho_j(p_<=K)=0` globally as well.
