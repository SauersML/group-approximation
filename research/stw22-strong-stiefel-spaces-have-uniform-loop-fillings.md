---
rg: 2
id: stw22-strong-stiefel-spaces-have-uniform-loop-fillings
kind: claim
title: Hyperfinite strong Stiefel spaces have a trace-uniform small-loop filling modulus
distinct_from:
  stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling: that theorem transfers a hypothetical unweighted filling modulus to weighted purification fibres; the present theorem proves the unweighted modulus.
  stw22-one-dimensional-trivial-field-trace-continuity: that theorem needs only paths between two points; the present theorem continuously lifts and fills an entire loop.
  stw22-lwcl-on-fixed-support-strata: that theorem gives local sections for one continuously varying support field; the present theorem is uniform over every initial projection below a fixed target corner.
artifacts:
  - research/artifacts/stw22-uniform-stiefel-loop-filling-audit-2026-08-30.md
---

Let `R` be the hyperfinite `II_1` factor and let `e in R` be a nonzero
projection.  For every projection `p in R` with `tau(p)<=tau(e)`, put

```text
V(p,e)={v in eR:v^*v=p}.
```

There is a universal modulus `rho:(0,infinity)->(0,infinity)` with the
following property.  If `v_0 in V(p,e)` and a continuous loop

```text
v:S^1->V(p,e)
```

satisfies, for some `epsilon>0`,

```text
sup_z ||v(z)-v_0||_2<rho(epsilon),
```

then it has a continuous filling `V:D^2->V(p,e)` satisfying

```text
sup_y ||V(y)-v_0||_2<epsilon.                           (USF)
```

The same modulus works for every `p` and `e`; in particular it is
uniform when `tau(p)<=s<tau(e)`.  Thus the property `(USF_1)` from
`stw22-weighted-equi-lc1-reduces-to-unweighted-stiefel-filling` holds.

The proof has two quantitative steps.  A loop of nearby frames admits a
continuous unitary lift which stays uniformly close to the identity.  This
is obtained from the controlled one-dimensional Michael selection theorem,
applied to the lower-semicontinuous family of conjugator fibres; it does not
use a quotient or orbit cross-section.  Applying the Popa--Takesaki
contracting semigroup in the whole target corner contracts the lifted loop,
and hence fills the frame loop, without increasing its `2`-norm radius.
