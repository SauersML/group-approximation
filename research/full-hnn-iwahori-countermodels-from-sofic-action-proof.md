---
rg: 2
id: full-hnn-iwahori-countermodels-from-sofic-action-proof
kind: route
title: Correct the two modular vertices inside canonical sofic HNN models
target: sofic-dyadic-action-produces-full-hnn-iwahori-countermodels
requires:
  - sofic-dyadic-coset-action-makes-hnn-sofic
  - sl2-z-same-dimension-hs-stable
---

Under the action-soficity hypothesis, the first dependency supplies
canonical permutation microstates of the full HNN group.  Restrict them to
the two modular vertex presentations.  Same-dimensional HS stability of
`SL_2(Z)=C_4*_(C_2)C_6` changes each restriction by `o(1)` to an exact unitary
representation.  Consequently the common edge remains `o(1)`-matched, all
fixed-word traces keep their canonical limits, and the stable letter still
asymptotically commutes with the first vertex.

For `a` in the second vertex but outside the amalgamated edge, Britton's
lemma gives `[t,a]!=1`.  Hence canonicality gives

```text
||[T_n,pi_(n,-)(a)]||_2^2
 = 2-2 Re tr([T_n,pi_(n,-)(a)]) -> 2.                 (FHC4)
```

Finally use the graph projection `(FHC2)`.  It has rank exactly half the
doubled dimension, and direct block multiplication proves `(FHC3)`.  It is
therefore a positive-rank, positive-corank projection centralizer of the
first exact vertex which the second exact vertex moves by a fixed amount.
