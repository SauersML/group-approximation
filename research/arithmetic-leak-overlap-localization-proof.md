---
rg: 2
id: arithmetic-leak-overlap-localization-proof
kind: route
title: Conjugate the overlap through the relative commutator and telescope fixed words
target: arithmetic-leak-commutator-localizes-in-overlap-commutant
requires: []
---

Put `H=pi(h)`.  For `m in M`, choose `n in Lambda` with `m=hnh^(-1)`.
Writing `M_0=pi(m)` and `N_0=pi(n)`, exactness gives
`H^* M_0 H=N_0`.  Since `U` commutes with both `M_0` and `N_0`,

```text
(U H U^* H^*) M_0 (H U H^* U^*)
 = U H U^* N_0 U H^* U^*
 = U H N_0 H^* U^*
 = U M_0 U^*
 = M_0.
```

This proves `(OL1)`.

For `(OL2)`, repeat the same four replacements.  Evaluation of each fixed
equality word differs by at most its fixed van Kampen area times `delta`.
Almost-commutation with a fixed `Lambda` word telescopes with the word's
fixed length from the errors on `S_Lambda`.  Left and right multiplication
by unitaries preserve normalized Hilbert--Schmidt norm.  Summing the
finitely many replacement errors and taking the maximum over the fixed
set `S_M` gives one dimension-independent constant `C`.

For `SL_3(Z)<SL_3(Z[1/p])`, commensuration makes `M` finite index.  If the
hypothesis is initially projective trace-square centrality, the perfectness
estimate `(PTS4)` in `projective-trace-square-transfer-for-sl3-pair` first
converts it to the ordinary almost-commutation used in `(OL2)`.

