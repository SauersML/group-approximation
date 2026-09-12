---
rg: 2
id: fpbs-nonuniqueness-parameter-criterion
kind: claim
title: On a nonamenable quasi-transitive graph strict thresholds are equivalent to one nonuniqueness parameter
distinct_from:
  fpbs-benjamini-schramm-universal: that is the universal every-generating-set goal; this is the pointwise reduction of the single-graph statement p_c<p_u to the existence of one parameter with infinitely many infinite clusters, valid for one fixed graph.
---

**ESTABLISHED.** Let `G` be a connected, locally finite, nonamenable
quasi-transitive graph. Then

```text
p_c(G) < p_u(G)   if and only if   N_infinity(p) = +infinity for some p.
```

This reduces the single-graph nonuniqueness question to exhibiting one
parameter at which infinitely many infinite clusters occur. It is the pointwise
content behind `fpbs-benjamini-schramm-universal`: to prove the goal for a
given Cayley graph it suffices to produce one nonuniqueness parameter, and the
number `N_infinity` there is automatically `+infinity` rather than an
intermediate value.

The equivalence is standard and used implicitly across the fpbs region; this
node states it as a reusable reduction so that both cost-side and operator-side
routes can target "one nonuniqueness parameter" rather than the threshold gap
directly.

DERIVATION
fpbs-nonuniqueness-parameter-criterion-proof
