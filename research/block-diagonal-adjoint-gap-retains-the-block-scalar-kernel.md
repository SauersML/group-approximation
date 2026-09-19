---
rg: 2
id: block-diagonal-adjoint-gap-retains-the-block-scalar-kernel
kind: claim
title: Block-diagonal adjoint spectral gaps retain the whole block-scalar kernel
artifacts:
  - research/artifacts/section-three-quantitative-no-go-audit-2026-08-21.md
distinct_from:
  word-recursion-cannot-amplify-sublinear-summands: that proves direct-sum naturality for arbitrary bounded word packets; this identifies the exact kernel of the adjoint spectral-gap operator and shows why even perfect within-block gaps do not help.
  property-t-does-not-force-marked-carrier-transversality: that gives a canonical group counterexample with a captured positive-density projection; this is a finite-matrix block calculation with arbitrary small block weights.
  hs-one-level-expander-block-decomposition: that seeks a decomposition into blocks with scalar gap on each block; this records why its conclusion cannot be read as one global scalar gap.
---

**ESTABLISHED.**  Let

```text
H=direct_sum_(b=1)^m H_b,       U_s=direct_sum_b U_(s,b),
```

and let `p_b` be the block projections.  For the adjoint Dirichlet form

```text
E_Ad(X)=sum_s ||[U_s,X]||_2^2,                          (BDG1)
```

one has

```text
span{p_1,...,p_m} subset ker(E_Ad).                    (BDG2)
```

Consequently, even if every block action has scalar adjoint gap at least
`gamma>0`, the global inequality can only have a gap relative to the
block-scalar algebra.  It has no positive gap relative to the global scalars
when `m>1`.

The same decomposition quantifies localized word error.  If a unitary word
`w(U)` is the identity outside a union `P` of blocks of normalized trace
`theta`, then

```text
||w(U)-1||_2^2<=4 theta.                               (BDG3)
```

Neither a within-block spectral gap nor property `(T)` changes the factor
`theta`, because `P` itself belongs to the adjoint kernel.  A spectral-gap
argument can delocalize error only after an independent coupling removes the
block projections from the commutant, or after a marked hypothesis gives
their union a fixed positive trace.
