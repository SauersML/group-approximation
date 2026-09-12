---
rg: 2
id: rstar-cap-selection-unstable-under-matrix-conj
kind: claim
title: Contextwise R-star cap selection is not stable under a finite matrix conjunction
distinct_from:
  fano-cap-witness-sections-force-source-affine-safety: that gives the support-affine necessary condition for one context and one supplied trace; this constructs a tracial non-RU BCS for which that obstruction occurs in every trace.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for a cap-supported trace in one particular hard family; this is a black-box compiler firewall and does not decide that source-specific assertion.
---

**ESTABLISHED BLACK-BOX FANO FIREWALL.**  Let `B_tilde` be the separated BCS
from `matrix-conj-forces-unsafe-support`.
Apply a contextwise exact pp reduction to `R_*`, of the kind used in the
Culf--Mastel fixed-language compiler, to its distinguished AND context.
Then no perfect trace of the lifted instance can have Fano-cap support in
every `R_*` occurrence of that gadget.

Indeed every lifted perfect trace restricts to a satisfying trace of
`B_tilde`.  The AND context therefore has positive support

```text
S=C={000,010,100,111},                                   (CFC1)
```

and `Aff(S)` contains the forbidden source assignment `110`.  If every target
occurrence were cap-supported, choose one positive target witness under each
of the four positive source atoms.  By
`fano-cap-witness-sections-force-source-affine-safety`, those witnesses would
imply

```text
Aff(S) subseteq C,                                      (CFC2)
```

contradicting `(CFC1)`.

Thus cap selection cannot be a black-box consequence of tracial
satisfiability, non-`R^U` soundness, factoriality, uniqueness of trace, or
global support minimality, even after allowing arbitrary witness choices in
the fixed-language pp gadget.  It can still hold for the particular
Culf--Mastel HALT presentation, but a proof must exploit source-specific
support geometry that is destroyed by this harmless finite-dimensional
conjunction.
