---
rg: 2
id: stw22-dimension-two-weighted-selection-and-colouring-proof
kind: route
title: Apply two-dimensional Michael selection to the weighted fibres and then colour the local lifts
target: stw22-two-dimensional-trivial-field-trace-continuity
requires:
  - stw22-one-dimensional-trivial-field-trace-continuity
  - stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling
  - stw22-finite-dimensional-colouring-from-local-lifts
artifacts:
  - research/artifacts/stw22-low-spectrum-boundary-extension-audit-2026-08-30.md
---

Use the notation of
`stw22-cross-stratum-selection-in-dimension-one-proof`.  For fixed
`s<tau(e)`, that proof establishes that the weighted-purification
multifunction

```text
F(a)={w in eR:w^*w=a},
0<=a<=1,       tau(supp(a))<=s,
```

has nonempty closed values in the complete operator-norm unit ball of
`L^2(R)`, is lower semicontinuous, and has path-connected values forming a
uniformly equi-`LC^0` family.  Those arguments do not use the dimension of
the parameter space.

The new input
`stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling` gives a
single small-loop filling modulus for all these fibres.  Moreover every
loop in an individual fibre is null-homotopic: apply
`stw22-low-spectrum-weighted-boundary-filling` with the constant target
projection `e` and with `b=a`.  Thus the values are `C^1` and form an
equi-`LC^1` family.

Michael's finite-dimensional selection theorem, in its `n=1` case, now
applies to every paracompact parameter space `Z` with `dim(Z)<=2`.  Hence
every `2`-norm-continuous field `a:Z->R_+` satisfying the displayed support
bound has a continuous weighted purification into `e`.  In particular the
local weighted corner-lifting hypothesis `(LWCL)` of
`stw22-finite-dimensional-colouring-from-local-lifts` holds whenever the
base has dimension at most two.

Apply that theorem with `d=2`.  Its three-colour replication estimate kills
every bounded positive trace on every fibre gap `K_x/J_x`.  Finally
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` identifies every
trace on the completion with integration of the fibre trace against a
probability measure and proves uniform-`2`-norm continuity.

The route remains a valid dimension-two proof.  Its dimensional bound is
superseded by `stw22-finite-dim-weighted-selection-proof`, which applies the
same Michael and colouring steps using all finite sphere degrees.
