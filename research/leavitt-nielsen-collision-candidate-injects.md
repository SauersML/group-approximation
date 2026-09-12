---
rg: 2
id: leavitt-nielsen-collision-candidate-injects
kind: claim
title: The Nielsen-collision length-six Leavitt word has four light same-sign corners and injects over every group
distinct_from:
  leavitt-length-six-nielsen-collision-candidate: that constructs the word and its Nielsen gate collision; this proves the word cannot violate Kervaire--Laudenbach, because its star graph already passes the four-corner weight test.
  leavitt-three-gate-candidate-is-injective: that fences the earlier three-gate word through a Nielsen amalgam; this fences the collision word by star-graph weights, without using any Nielsen map.
---

The word `(NC1)` of `leavitt-length-six-nielsen-collision-candidate` is

```text
W_col = a t^2 a t p t e t^(-1) q t^(-1)       over  G = EL_20(L_(F_2)(1,2)),
a = x_12(s_0),  e = x_12(t_1),  p = (1 2 ... 20),  q = x_34(s_1) x_(11,12)(t_0).
```

Coefficient injectivity holds for it: `G -> (G * <t>)/<<W_col>>` is injective,
and every reduced spherical picture over `<G, t | W_col>` is empty. So
`W_col` is not a Kervaire--Laudenbach counterexample.

The deliberate Nielsen gate collision that selected this word does not change
its star graph. After splitting `t^2`, the four same-sign corners carry the
labels `1, a, p` (P) and `q` (N). No two of them close a trivial 2-cycle, so
part 1 of `kl-four-same-sign-corner-words-inject` applies with `r = 4`. That
part allows involution loops, and the loop coefficients `a` and `e` are
involutions.

Consequence for the search: selecting candidates by Nielsen-table collisions
is not enough. A surviving length-six candidate must close a same-sign
coincidence, i.e. repeat a P-label or put a P-label inverse to an N-label.
See `kl-length-six-one-coincidence-words-inject` for what one coincidence
still requires.

DERIVATION
leavitt-nielsen-collision-light-corners-proof
