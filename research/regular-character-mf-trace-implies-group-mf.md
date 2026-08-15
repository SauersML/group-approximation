---
rg: 2
id: regular-character-mf-trace-implies-group-mf
kind: claim
title: An MF regular character forces the group to be operator MF
distinct_from:
  countable-group-mf-conventions: That claim compares group-level MF formulations at fixed accuracy; this one converts a trace-level property of the full group C-star algebra into the group-level one.
  mf-implies-hyperlinear: That root asks the converse-flavoured question, whether operator-norm models can be given faithful traces; this claim says that if the canonical trace already has norm microstates then the group is MF.
artifacts:
  - GroupApproximation/Sofic/MFDefinitions.lean
---

Let `G` be a countable group, `A = C^*(G)` its full group C-star algebra and
`tau` its canonical trace (`tau(u_g) = 1` if `g=1`, else `0`).  If `tau` is an
**MF trace** in the sense of Shulman, arXiv:2507.22783v3 --- maps
`phi_n : A -> M_(k_n)` with

```text
||phi_n(ab)-phi_n(a)phi_n(b)|| -> 0,
||phi_n(la+mb)-l phi_n(a)-m phi_n(b)|| -> 0,
||phi_n(a^*)-phi_n(a)^*|| -> 0,
sup_n ||phi_n(a)|| < infinity,
|tau(a)-tr(phi_n(a))| -> 0,
```

all norms being the operator norm --- then `G` is operator MF in the weak
Carrion--Dadarlat--Eckhardt sense.

The point is that the trace normalization does all the work that the weak MF
definition cannot do by itself: `tr(phi_n(1)) -> 1` pins the unit corner at
relative dimension `1`, and `tr(phi_n(u_g)) -> 0` gives separation
automatically, with constant `sqrt 2`.  Equivalently: an MF regular character
is exactly a trace-controlled MF model in Schafhauser's sense, and those do
give both the norm and the trace clause.
