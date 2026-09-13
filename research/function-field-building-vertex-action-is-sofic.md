---
rg: 2
id: function-field-building-vertex-action-is-sofic
kind: claim
title: The action of SL_3(F_2[t,1/t]) on the type-zero vertices of the SL_3(F_2((t))) building is sofic
distinct_from:
  sl3-dyadic-building-vertex-action-is-sofic: that is the number-field action of SL3(Z[1/2]) on the Q_2 building; this is the positive-characteristic one-place Laurent action, which is a sub-action of the Kun--Thom opposite slice
  function-field-hecke-pair-is-relatively-embeddable: that is the operator-algebraic statement; this is the permutation statement, which is sufficient for it
---

**OPEN.**  Put `Lambda=SL_3(F_2[t,1/t])` and `C=SL_3(F_2[t])`.  The coset
action `Lambda action Lambda/C` is sofic in the sense of GKP Definition
2.1(5).  It is the action on the type-zero vertices of the Bruhat--Tits
building of `SL_3(F_2((t)))`.

## Attempts

- **Exact finite actions.**  Excluded.  `C` is Kazhdan and co-dense in every
  finite quotient (TR1), so
  `codense-kazhdan-coset-action-forces-permutation-outliers` applies.
- **Building quotients and random lifts.**  The dyadic label fence
  `sl3-finite-building-quotients-forget-arithmetic-labels` transfers
  verbatim: a fixed arithmetic label descends to a finite quotient only if it
  normalizes the deck group.
- **Compression.**  `C` is incompressible in `Lambda`, so the Kun--Thom
  Theorems A, C and 4.1 cannot give nonsoficity.
- **Positive-characteristic structure.**  One could use the Soulé sector
  fundamental domain of `C` at the place `1/t`, or the Curtis--Tits colimit
  presentation of the affine Kac--Moody group `Lambda`.  Neither has been
  turned into approximate labelled models.
- **Exact approximants of the pair.**  Excluded as well, and not only exact
  actions of `Lambda` itself.  `Lambda` is finitely presented
  (`laurent-s-arithmetic-finiteness-lengths`) and `C` is finitely generated.
  Items 5 and 7 of `sofic-coset-actions-pass-to-marked-colimits` then show
  that `(Lambda,C)` is not a limit of marked pairs with separable
  stabilizers, and in particular not an LEF pair.  Any sofic model is a
  non-group almost-action.  By
  `codense-tau-coset-soficity-forces-permutation-instability`, such a model
  also witnesses that `Lambda` is not flexibly permutation-stable.
  (Lane `ex2-hecke-pair-positive`, 2026-09-13.)
- **Rank-one corner.**  A necessary condition is
  `function-field-rank-one-vertex-action-is-sofic`, the `SL_2` corner orbit.
  It escapes the finite-presentation stop, because `SL_2(F_2[t,1/t])` is not
  finitely presented and `SL_2(F_2[t])` is not finitely generated.  There
  the colimit route reduces soficity to separability in truncated virtually
  free amalgams (`sl2-laurent-f2-amalgam-approximants-separate-the-vertex`).
