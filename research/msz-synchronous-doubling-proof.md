---
rg: 2
id: msz-synchronous-doubling-proof
kind: route
title: Apply synchronous conjugation control to the polynomial doubling recurrence
target: msz-polynomial-doubling-survives-synchronous-states
requires:
  - msz-polynomial-doubling-star-algebra-compiler
  - synchrony-replaces-tracial-cyclicity-at-sobolev-cost
artifacts:
  - research/artifacts/mehta-slofstra-zhao-positivity-ingestion-2026-08-20.md
---

This is Mehta--Slofstra--Zhao Proposition 6.3.  Their proof first applies
Lemmas 3.7 and 3.8 to compare the two conjugate carrier norms and bound the
mixed real part.  The explicit degree bounds

```text
deg(X_tilde_n)=4n+1,
||P_tilde_n||_(1,1)<=2n+2,
||X_tilde_n P_tilde_n X_tilde_n||_(1,1)<=10n+4
```

give the displayed additive term `(25n+25)sqrt(epsilon)`.  Lemma 3.9 and the
polynomial decomposition of `(MSD1)` pay the recurrence error.  Iterating
`(MSY2)` and discarding the bounded terminal term proves `(MSY1)`.
