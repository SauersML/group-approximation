---
rg: 2
id: shift-raag-family-classifies-amenability
kind: claim
title: The two-generator groups in which a commutes with its prescribed t-conjugates are amenable exactly when every positive conjugate is prescribed
distinct_from:
  centralizing-hnn-over-conjugate-basis-is-rf-iff-index-set-closed: that family has a third generator centralizing conjugates and is decided by profinite closure; this family is two-generated, has the conjugates commute among themselves, and is decided by completeness of a graph, so amenability rather than residual finiteness is what the index set controls.
  centralizing-hnn-over-conjugate-basis-is-always-sofic: that uses a right-angled Artin kernel to prove soficity; this uses a right-angled Artin kernel to decide amenability, through the fact that a right-angled Artin group is amenable iff its graph is complete.
---

ESTABLISHED.  For `J <= Z_{>0}` put

```text
G_J = < a, t | [a, t^j a t^-j] = 1,  j in J >.                        (SR1)
```

Then, with `a_i = t^i a t^-i` and `Gamma_J` the graph on `Z` with edges
`{i, i+j}` for `j in J`,

```text
G_J = A(Gamma_J) x| Z    (shift action), and
G_J amenable  iff  G_J metabelian  iff  G_J ~= Z wr Z  iff  J = Z_{>0};
G_J contains a free subgroup of rank two  iff  J != Z_{>0}.           (SR2)
```

So one two-generator family, recursively presented uniformly in an
enumeration of `J`, realizes the Tits-type alternative "amenable or
contains `F_2`" as a computable switch controlled by whether an r.e. set
is everything.  It feeds
[[amenability-two-generator-recursive-is-pi2-complete]].
