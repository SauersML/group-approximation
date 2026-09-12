---
rg: 2
id: stw22-stabilized-dimension-three-diffuse-selection-proof
kind: route
title: Apply factor-uniform degree-two selection to stabilized diffuse-factor weighted fibres
target: stw22-dim3-diffuse-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-diffuse-weighted-copy-uniform-s2-fillings
  - stw22-all-finite-factor-weighted-copy-uniform-loop-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

Fix a positive contraction `a in M`, a replication number `m`, and
`gamma>0` such that

```text
m tau_x(supp(a_x))<=1-gamma             for every x in K.   (D3-3)
```

## 1. The varying fibres live in one complete space

Apply `stw22-dim1-factor-bundles-have-uniform-traces`.
The countably generated Hilbert `C(K)`-module embeds as a complemented
submodule of `C(K,ell^2)`. The exact weighted-copy sets

```text
F_x(a)={(v_1,...,v_m):v_j^*v_j=a_x,
        (v_iv_i^*)(v_jv_j^*)=0 for i!=j}              (D3-4)
```

are therefore nonempty closed subsets of the fixed complete Hilbert space
`(ell^2)^m`, and `x |-> F_x(a)` is lower semicontinuous. Closedness is
taken inside the fibre operator unit balls, where products are continuous
from `L^2` to `L^1`. The quantitative correction estimate proving lower
semicontinuity is uniform over all finite factors and preserves exactly
the relations in (D3-4).

Countable generation makes each `L^2(M_x)` separable, hence each II1
factor `M_x` has separable predual. Thus the fibre theorem applies at
every `x`.

## 2. The values satisfy the degree-two Michael hypotheses

Use the Hilbert-sum metric on `(ell^2)^m`. The factor-uniform path theorem,
`stw22-all-finite-factor-weighted-copy-uniform-loop-fillings`, and
`stw22-diffuse-weighted-copy-uniform-s2-fillings` give common local
moduli in degrees `0,1,2`, respectively. The same results give path,
simple, and two-connectivity of every value. Their control is independent
of `x`, the fibre isomorphism type, the weight, `m`, and the slack in
(D3-3).

If the stabilization argument is expressed with the maximum tuple metric,
the two metrics obey

```text
d_max<=d_sum<=sqrt(m)d_max.                            (D3-5)
```

For the already fixed `m`, the usual ambient-centre conversion (choose a
point of a sphere in the fibre value, halve the output radius, and use
(D3-5)) transfers those fibre-centred moduli to equi-`LC^2` in the common
ambient Hilbert space.

Compact Hausdorff spaces are paracompact. Michael's finite-dimensional
selection theorem with `n=2`, applied to the lower-semicontinuous closed
two-connected equi-`LC^2` family (D3-4), gives a continuous exact tuple
over `K` because `dim(K)<=3`.

## 3. Recover operators and kill the fibre gaps

The selected tuple is initially a section of the stabilized Hilbert
module. Each component lies fibrewise in the operator unit ball. The
operator-ball identity `(OB)` in
`stw22-dim1-factor-bundles-have-uniform-traces` therefore
puts every component back in `M_1`; no norm-continuity assertion is used.
Hence (D3-4) holds globally in `M`.

Now choose a positive contraction lift `b in K_(x_0)` of a positive
class in the fibre gap, fix the spectral cut `c=(b-epsilon)_+`, and let
`m>=1`. Since the lift `b` is `2`-null at `x_0`,
Chebyshev and continuity give a neighbourhood on which

```text
tau_y(supp(c_y))<1/(2m).                               (D3-6)
```

Multiply by a central cutoff which equals one near `x_0` and vanishes
off that neighbourhood. The resulting global
positive contraction has the same gap class near `x_0` and satisfies
(D3-3) with `gamma=1/2`. The selected `m` orthogonal exact copies imply,
for every bounded positive trace `sigma` on the gap,

```text
m sigma([c])<=||sigma||.                               (D3-7)
```

Indeed the sum of the `m` orthogonal range positives is itself a positive
contraction, which is the last inequality in (D3-7).

First let `m` tend to infinity and then let `epsilon` decrease to zero.
Every positive gap trace vanishes. The exact fibre-gap criterion
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` yields (D3-2)
and uniform `2`-continuity.

The diffuse hypothesis is used precisely in the degree-two fibre theorem.
All corners and `M_m(M_x)` remain diffuse II1 factors. Matrix stabilizers
can carry nonzero fundamental group, so this proof gives no claim for a
matrix fibre or a mixed bundle.