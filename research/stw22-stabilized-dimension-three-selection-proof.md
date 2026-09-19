---
rg: 2
id: stw22-stabilized-dimension-three-selection-proof
kind: route
title: Apply the all-factor degree-two modulus in the stabilized L2 bundle
target: stw22-dim3-factor-bundles-have-uniform-traces
requires:
  - stw22-dim1-factor-bundles-have-uniform-traces
  - stw22-all-finite-factor-weighted-copy-uniform-s2-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim3-all-factor-bundle-breakthrough-2026-08-31.md
---

Fix `m>=1`, `gamma>0`, and a positive contraction `a in M` with

```text
m tau_x(supp(a_x))<=1-gamma            for every x in K.    (AF3-2)
```

The stabilization theorem embeds the countably generated Hilbert
`C(K)`-module completion into `C(K,ell^2)` and puts the exact
weighted-copy values `F_x(a)` in the one complete space `(ell^2)^m`.
It proves that these values are nonempty, closed in the fibre operator
unit balls, and lower semicontinuous, with estimates uniform over every
finite factor. It also proves the operator-ball recovery identity needed
after selection.

Countable generation makes each fibre `L^2(M_x)` separable, so each
diffuse fibre has separable predual; matrix fibres are automatically
separable. The all-factor path, loop, and two-sphere theorems therefore
give common local moduli in degrees `0,1,2` and show that every value is
two-connected. For fixed `m`, the maximum and Hilbert-sum tuple metrics
are uniformly equivalent. The standard ambient-centre conversion thus
makes the family equi-`LC^2` in `(ell^2)^m`.

Michael's finite-dimensional selection theorem with `n=2` applies because
`K` is paracompact, `dim(K)<=3`, and the values are nonempty, closed,
two-connected, lower semicontinuous, and equi-`LC^2`. It produces a
continuous exact weighted-copy tuple. Operator-ball recovery places its
components in `M_1`.

No continuity of fibre type is required. At each `x`, the common
degree-two modulus is supplied by the matrix branch or the diffuse branch;
lower semicontinuity across points where type or matrix size changes was
already proved by the type-free finite-factor correction estimate. Michael
selection uses only the common modulus, not a continuous choice of its
proof.

Finally, choose a positive contraction lift `b in K_(x_0)` of a positive
fibre-gap class, fix `epsilon>0`, and let `m` be arbitrary. The cut
`c=(b-epsilon)_+` has support trace below `1/(2m)` on a neighbourhood of
`x_0`. A central cutoff equal to one near `x_0` and zero off that
neighbourhood turns it into a global element satisfying (AF3-2) with
`gamma=1/2` without changing its gap class. The selected `m` exact copies
have orthogonal range positives whose sum is a positive contraction, so

```text
m sigma([c])<=||sigma||                                (AF3-3)
```

for every bounded positive trace `sigma` on the gap. Let `m` tend to
infinity and then `epsilon` decrease to zero. Every gap trace vanishes,
and the exact fibre-gap criterion gives (AF3-1).