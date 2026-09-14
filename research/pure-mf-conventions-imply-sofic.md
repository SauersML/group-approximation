---
rg: 2
id: pure-mf-conventions-imply-sofic
kind: claim
title: Every pure representation-field MF convention forces soficity
distinct_from:
  countable-group-mf-conventions: that proves the five representation-field conventions imply operator MF; this proves each of them also forces maximal almost periodicity and hence soficity, so none of them can be carried by a nonsofic group.
---

ESTABLISHED.  Let `G` be countable.  If `G` is PMatF, that is, there are
genuine finite-dimensional unitary representations `pi_n` of `G` with
`||pi_n(c)|| -> ||lambda(c)||` for every `c` in the complex group ring, then

```text
finite-dimensional unitary representations separate the points of G,
every finitely generated subgroup of G is residually finite,
G is sofic.
```

The same conclusion holds for trace-free PPermF, trace-PMF, PFF and PPF, since
each of them implies PMatF in
`GroupApproximation/Sofic/MFRepresentationVariants.lean`.

**Consequence.**  None of these five conventions can separate MF from
soficity.  A nonsofic MF group can exist only in conventions whose models are
approximate rather than genuine representations.  Operator MF is such a
convention and does separate (`weak-mf-does-not-imply-sofic`).
