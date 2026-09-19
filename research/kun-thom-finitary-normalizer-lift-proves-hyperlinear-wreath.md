---
rg: 2
id: kun-thom-finitary-normalizer-lift-proves-hyperlinear-wreath
kind: route
title: Lift the finitary symmetric action and restrict the resulting hyperlinear extension to the Kun--Thom wreath
target: hyperlinear-wreath-model
requires:
  - kun-thom-finitary-action-lifts-to-normalizer
  - finitary-extension-ce-iff-action-lifts-to-normalizer
  - wreath-candidate-embeds-in-finitary-permutation-extension
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

The trace-correct normalizer lift makes

```text
R rtimes_alpha G = L(Sym_fin(X x {0,1}) rtimes G)
```

Connes embeddable.  Hence the finitary permutation extension is
hyperlinear.  By `wreath-candidate-embeds-in-finitary-permutation-extension`
it contains the Kun--Thom wreath `W`, and hyperlinearity passes to
subgroups.  Thus `W` is hyperlinear.

This implication is deliberately one-way.  Nothing here claims that an
embedding of `L(W)` extends to the larger crossed product, and the route
does not disguise the normalizer-lift claim as a permanence theorem.
