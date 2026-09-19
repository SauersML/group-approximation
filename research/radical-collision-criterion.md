---
rg: 2
id: radical-collision-criterion
kind: claim
title: A sofic-radical element with a hyperlinear detector yields a hyperlinear nonsofic group
distinct_from:
  sofic-radical-linear-action-criterion: That theorem recognizes membership in the sofic radical from finite actions; this theorem converts membership plus one hyperlinear detector into a separating group.
  hyperlinear-nonsofic-group: This is the reusable implication; the other asks for an explicit input satisfying its hypotheses.
  simple-sofic-total-mf-radical: This concerns the sofic and hyperlinear radicals and produces a nonsofic range; the other constructs a simple sofic group with total MF radical.
artifacts:
  - GroupApproximation/Sofic/HyperlinearResidualDetector.lean
  - GroupApproximation/Sofic/RadicalSeparation.lean
  - notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md
---

If a countable group `H` contains an element

```text
x in Rad_sof(H) minus Rad_hyp(H),
```

then a hyperlinear nonsofic group exists.  Indeed, choose a hyperlinear
detector of `x` and restrict its codomain to the image of `H`.  That image is
hyperlinear.  It cannot be sofic, because the quotient map from `H` would
then have to kill `x`.
