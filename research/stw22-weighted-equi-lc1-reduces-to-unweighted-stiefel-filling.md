---
rg: 2
id: stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling
kind: claim
title: Weighted loop filling reduces to strong-Stiefel filling and a low-spectrum extension
root: true
distinct_from:
  stw22-one-dimensional-trivial-field-trace-continuity: that theorem proves uniform local path connectedness and settles bases of dimension at most one; the present theorem identifies the additional, genuinely two-dimensional uniform filling property.
  stw22-lwcl-on-fixed-support-strata: that theorem gives local sections on a continuous fixed-support stratum; the present theorem concerns uniform null-homotopies of loops simultaneously over all support traces below a fixed corner.
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem conditionally turns local weighted lifts into trace vanishing; the present theorem isolates an equivalent operator-topological condition for obtaining those lifts in dimension two.
artifacts:
  - research/artifacts/stw22-dimension-two-stiefel-filling-obstruction-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor, let `e in R` be a projection,
and fix `s<tau(e)`.  For a projection `p` with `tau(p)<=s`, put

```text
V(p,e)={v in eR:v^*v=p},
```

with the `2`-norm metric.  Consider the uniform Stiefel filling property

```text
(USF_1) For every epsilon>0 there is delta>0, independent of p,
        such that every loop in V(p,e) contained in a delta-ball
        about one of its points fills in the corresponding epsilon-ball.
```

Then `(USF_1)`, together with
`stw22-low-spectrum-weighted-boundary-filling`, implies the following global
metric-uniform loop filling property for the family of weighted purification fibres

```text
F(a)={w in eR:w^*w=a},
0<=a<=1,       tau(supp(a))<=s.                         (WPF)
```

Namely, for every `epsilon>0` there is one `delta>0` such that every loop
in one `F(a)` contained in a `delta`-ball about a point of that fibre fills
in the corresponding `epsilon`-ball.  This global uniform property implies
Michael's equi-`LC^1` hypothesis and hence is a sufficient dimension-two
selection criterion.  Conversely, the weighted property implies `(USF_1)`
by restricting to projection weights.  The only unresolved implication is
the relative extension of continuous low weighted frames when their polar
frames are discontinuous.

The unweighted modulus is now established by
`stw22-strong-stiefel-spaces-have-uniform-loop-fillings`.  This weighted
claim remains open because weighted `2`-norm continuity near zero spectrum
does not imply ordinary `2`-norm continuity of the polar frames.
Accordingly, no dimension-two trace theorem is asserted here.
