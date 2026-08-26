---
rg: 2
id: arithmetical-complexity-table-of-group-properties
kind: claim
title: Where the approximation, residual, amenability and rigidity properties of groups sit in the arithmetical hierarchy, by syntax
artifacts:
  - GroupApproximation/Computability/AmenableEnumeratedHardness.lean
  - GroupApproximation/Computability/HyperlinearEnumeratedHardness.lean
  - GroupApproximation/Computability/RFEnumeratedHardness.lean
  - GroupApproximation/Computability/RFPresentationPi02.lean
  - GroupApproximation/Computability/HyperlinearUndecidabilityRoute.lean
  - GroupApproximation/Computability/ProfinitelyClosedIndexSet.lean
  - GroupApproximation/Computability/LEFEnumeratedPi02.lean
  - GroupApproximation/Computability/SoficEnumeratedPi02.lean
  - research/artifacts/arithmetical-complexity-note-2026-08-26.tex
  - research/artifacts/second-level-rice-theorem-2026-08-26.md
distinct_from:
  second-level-rice-theorem-for-local-approximation-properties: that is one theorem; this is the ledger of all classifications, including the ones outside its scope (residual finiteness, amenability, property (T)), with every cell pointing at its proof and every open cell named.
  approximation-property-recognition-dichotomy: that is the conditional row for hyperlinearity; this places it beside the unconditional rows.
---

ESTABLISHED (as a ledger; each cell is a separate established claim, and the
cells marked OPEN are open claims).  Syntaxes: `fp` = finite presentations,
`rec2` = two-generator recursive presentations (`rec3`, `rec` = three
generators, finitely many generators), `V` = pairs of words in Higman's
universal finitely presented group, `enum` = countably generated
enumerated presentations.

```text
property           fp                          rec2 / rec                    enum
-------------------------------------------------------------------------------------
trivial            Sigma^0_1-complete (folk.)  Pi^0_2-complete (folk.)       Pi^0_2-complete
sofic              Pi^0_2 \ Pi^0_1, complete   Pi^0_2-complete               Pi^0_2-complete
                   OPEN [S]
operator-MF        Pi^0_2-complete [MF]        Pi^0_2-complete               Pi^0_2-complete
LEF                = RF_fp                     Pi^0_2-complete               Pi^0_2-complete
hyperlinear        trivial or Sigma^0_1-hard   trivial or Pi^0_2-complete    same
                   in Pi^0_2 \ Pi^0_1 [H]      [H]
weakly sofic,      as hyperlinear              as hyperlinear                same
linear sofic       (in Pi^0_2 \ Pi^0_1) [W]    (trivial or complete) [W]
finitely           --                          Sigma^0_2-hard, in Sigma^0_3  Sigma^0_2-hard, in Sigma^0_3
presentable                                    [FP]
amenable           Pi^0_2 \ Pi^0_1, complete   Pi^0_2-complete               Pi^0_2-complete
                   OPEN [A]
metabelian         Pi^0_2 (complete OPEN)      Pi^0_2-complete               Pi^0_2-complete
contains F_2       Sigma^0_2 (lower: Pi^0_1-h) Sigma^0_2-complete            Sigma^0_2-complete
residually finite  Pi^0_2 \ Pi^0_1, complete   Pi^0_3-complete               Pi^0_3-complete
                   OPEN [RF-Higman]
residually p       Pi^0_2 \ Pi^0_1 (as RF)     Pi^0_3-complete               Pi^0_3-complete
property (T)       Sigma^0_1-complete          Sigma^0_1-complete (rec)      --
```

Legend.  `[S]` = [[sofic-safe-finite-presentation-compiler]];
`[MF]` = [[mf-recognition-finite-presentations-is-pi2-complete]];
`[H]` = [[approximation-property-recognition-dichotomy]], side (B) iff a
non-hyperlinear group exists;
`[A]` = [[amenability-of-finite-presentations-is-pi2-complete]];
`[W]` = [[weak-soficity-recognition-has-a-pi2-upper-bound]],
[[linear-soficity-recognition-has-a-pi2-upper-bound]] (side (B) iff some
group fails the property);
`[FP]` = [[finite-presentability-two-generator-recursive-is-sigma2-hard]];
`[RF-Higman]` = `Pi^0_2`-completeness of `RF_fp`, the residually finite
Higman problem.  Rows: sofic
[[sofic-recognition-two-generator-recursive-is-pi2-complete]],
[[sofic-recognition-finite-presentations-arithmetical-position]]; MF and LEF
[[mf-recognition-two-generator-recursive-is-pi2-complete]]; amenable,
metabelian, `F_2`
[[amenability-two-generator-recursive-is-pi2-complete]],
[[amenability-of-finite-presentations-arithmetical-position]]; residually
finite [[residual-finiteness-two-generator-recursive-is-pi3-complete]],
[[residual-finiteness-of-enumerated-presentations-is-pi3-complete]];
residually `p` [[residually-p-two-generator-recursive-is-pi3-complete]];
property (T) [[kazhdan-property-t-of-finite-presentations-is-sigma1-complete]];
the general engine [[second-level-rice-theorem-for-local-approximation-properties]].

Two structural readings.  (1) Every local approximation property lives at
level two on recursive presentations and is decided at level one only
trivially; the residual properties are one level higher on recursive
presentations, and collapse to level two only on finite presentations,
where the extra quantifier ("one finite quotient kills all relators") is
bounded.  (2) On finite presentations the exact level is known for (T)
(one, semidecidable) and unknown for every level-two candidate except MF,
each open cell being a form of a Higman-embedding question for that
property.

**Machine-checked cells.**  On enumerated presentation codes the sofic and LEF rows are kernel-checked as `Pi02Complete` (`SoficEnumeratedPi02.sofic_enum_pi02Complete`, `LEFEnumeratedPi02.lef_enum_pi02Complete`), the computability core of the residual-finiteness row as `ProfinitelyClosedIndexSet.pi03Complete_closedIndex`, and the hyperlinear finite-presentation equivalence as `HyperlinearUndecidabilityRoute.not_computablePred_iff_exists_nonhyperlinear_code`.

Also kernel-checked: `RFPresentationPi02.rf_fp_strict_position` (the residually finite finite-presentation cell), `RFEnumeratedHardness.rfCode_pi02Hard` (second-level lower bound on enumerated codes) and `HyperlinearEnumeratedHardness.hyperlinearCode_pi02Hard_of_exists`.

Amenability's second-level lower bound on enumerated codes is `AmenableEnumeratedHardness.amenableCode_pi02Hard`.
