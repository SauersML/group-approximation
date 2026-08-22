---
rg: 2
id: finite-nemesis-subcover-has-a-uniform-existential-residual-gap
kind: claim
title: A finite bespoke-nemesis subcover has one uniform optimized residual gap
distinct_from:
  bespoke-extension-nemesis-library-defeats-diagonal-schedules: that proves exact nonextension by closed-set compactness; this extracts a positive residual constant and records the correct semicontinuity statement.
  common-complete-approximation-specific-nemesis-compiler: that must construct an exhaustive enumerable library with one marked infinite completion; this is conditional on exhaustiveness and supplies neither construction nor completeness.
  finite-trace-profile-net-is-dimension-free: that compactifies scalar moment profiles; this optimizes over auxiliary-unitary extension types above each complete base type.
---

Use the notation of `bespoke-extension-nemesis-library-defeats-diagonal-schedules`.
For a finite gadget `E_i` with relator residual `G_i(x,y)>=0`, define on the
compact separated canonical type space `K_alpha`

```text
rho_i(x)=min { G_i(x,y) : (x,y) is a matricial-ultraproduct
                              joint extension type }.             (FER1)
```

The minimum exists.  The graph of admissible joint types is compact and
`G_i` is continuous.  Therefore

```text
{x : rho_i(x)<=c}
```

is compact for every `c`; equivalently `rho_i` is lower semicontinuous.  In
particular

```text
C_i={x:rho_i(x)=0}                                    (FER2)
```

is closed, and if `x notin C_i` then `rho_i(x)>0` on an open neighborhood of
`x`.

If the library is exhaustive, `(BEN1)`, compactness gives finite indices
`i_1,...,i_r` and one `epsilon>0` such that

```text
max_(1<=j<=r) rho_(i_j)(x) >= epsilon
                                      for every x in K_alpha.      (FER3)
```

Thus the finite sublibrary has a uniform robust nemesis gap even though the
winning gadget may depend on the complete extension type.  A standard
ultraproduct contradiction also yields a finite matrix-level version: after
choosing a sufficiently accurate finite base-relator/canonical-moment window,
every separated tuple has optimized residual at least `epsilon/2` for one of
these gadgets.  This last modulus is qualitative unless the compactness
argument is made effective.

## Quantifier fence

The optimized residual need not be continuous.  Infimizing a continuous
function over the fibers of an arbitrary compact correspondence gives lower
semicontinuity from compact projection, but upper semicontinuity requires a
lower-hemicontinuity or witness-lifting theorem for those fibers.  The proof
uses only lower semicontinuity, which is exactly the direction needed for a
robust positive nonextension neighborhood.

Moreover `(FER3)` is conditional on

```text
forall x exists i forall auxiliary y: G_i(x,y)>=epsilon_x,          (FER4)
```

not on `forall x forall i exists y`.  It does not manufacture the local
nemesis, authenticate a positive carrier, or prove that all gadgets share the
HALT witness.  Those are precisely the remaining compiler quantifiers.

