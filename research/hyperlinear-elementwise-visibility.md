---
rg: 2
id: hyperlinear-elementwise-visibility
kind: claim
title: Elementwise trace visibility is equivalent to hyperlinearity
distinct_from:
  sofic-implies-hyperlinear: That claim converts one approximation class into another; this one is an internal criterion which replaces joint near-maximal separation by one nontrivial element at a time.
  mf-implies-hyperlinear: That root asks whether operator-norm models exist with trace visibility; this claim only says that elementwise trace visibility already suffices, whatever produces it.
  hyperlinear-trace-not-mf-trace: That claim separates two classes of traces on one C-star algebra, using the non-MF witness; this one is a criterion for hyperlinearity of a group and says nothing about MF traces.
  hyperlinear-near-representation-criterion: Both characterize hyperlinearity, but this one is an in-repo criterion weakening joint separation to one element at a time, while the other is an external Kahl--Schneider theorem trading matrix microstates for an amenable near representation carrying an invariant charge.
artifacts:
  - GroupApproximation/Sofic/Hyperlinear.lean
  - GroupApproximation/Sofic/NormTraceGap.lean
---

Call `g != 1` in a countable group `G` *tracially visible* if there is a
constant `c_g>0` such that for every finite `F` in `G` and every `delta>0`
there is a finite-dimensional unitary map `phi:G->U(d)` with

```text
||phi(a)phi(b)-phi(ab)||_(2,norm) <= delta      (a,b in F),
Re tr_d(phi(g)) <= 1-c_g.
```

Then `G` is hyperlinear if and only if every `g != 1` is tracially visible.

The *near-maximal, jointly separated* half of this is already formalized:
`NormTraceGap.isHyperlinear_of_traced_normModels` builds a hyperlinear model
from an operator-norm model whose traces separate at the same accuracy `eps`,
its docstring recording that "the norm clause contributes multiplicativity and
nothing more".  What this claim adds is that an arbitrarily small constant
`c_g`, for one element at a time, is already enough.
In particular hyperlinearity never requires a single model separating all
elements at once, and the separation constant may be arbitrarily small: both
the near-maximal separation `2-epsilon` of `HyperlinearModel` and joint
separation are recovered from elementwise visibility with constants depending
only on `g`.
