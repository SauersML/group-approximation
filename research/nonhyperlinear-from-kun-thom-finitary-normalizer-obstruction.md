---
rg: 2
id: nonhyperlinear-from-kun-thom-finitary-normalizer-obstruction
kind: route
title: A non-splitting finitary-factor action makes its explicit nonsofic extension nonhyperlinear
target: non-hyperlinear-group
requires:
  - kun-thom-finitary-action-has-no-normalizer-lift
  - finitary-extension-ce-iff-action-lifts-to-normalizer
  - wreath-candidate-embeds-in-finitary-permutation-extension
artifacts:
  - notes/HYPERLINEAR_NONSOFIC_ATTEMPT_2026-08-26.md
---

Put

```text
Sigma_2 = Sym_fin((G/Gamma) x {0,1}) rtimes G.
```

The finitary-extension claim identifies
`L(Sigma_2)=R rtimes_alpha G`.  If the trace-correct normalizer lift does
not exist, the lifting criterion says this group von Neumann algebra is not
Connes embeddable.  Therefore `Sigma_2` is an explicit nonhyperlinear group.

The embedded Kun--Thom wreath is used only to record that `Sigma_2` is also
nonsofic; nonsoficity is not needed for the negative conclusion.  Together
with the positive route, this makes one normalizer-splitting decision a
literal fork between the two existence goals.
