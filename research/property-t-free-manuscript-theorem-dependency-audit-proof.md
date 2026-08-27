---
rg: 2
id: property-t-free-manuscript-theorem-dependency-audit-proof
kind: route
title: Read the current numbered statements and separate no-T algebra from two collapse obligations
target: property-t-free-manuscript-theorem-dependency-audit
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - metadata/NON_MF_SENTENCE_CENSUS.md
  - research/property-t-free-manuscript-results.md
  - research/property-t-free-el20-full-mf-radical.md
  - research/property-t-free-torsion-free-full-mf-radical.md
---

The current manuscript has three main theorems and fifteen numbered supporting
results.  Reading their statements and proofs gives the following exact split.

The results which are already independent of Property `(T)` are
`prop:mf-residual-calculus`, `thm:commutant`, `lem:stable-finite`,
`lem:central-corona-corner`, `lem:tau-elementary`, `prop:simple`,
`prop:defect`, `thm:hull`, `lem:saturation`, and `lem:simple-in-defect`,
together with the compressor-containment part of `prop:leavitt-compression`.

The results whose mathematical statements or proofs explicitly require
Kazhdan rigidity are `thm:compression-criterion`,
`lem:kazhdan-projection-order`, `thm:transport`, `cor:defect-hs`, and
`thm:normal-kazhdan`, plus the Property-`(T)` clauses of `thm:headline` and
`prop:leavitt-compression`.  A no-`(T)` replacement must remove this block;
renaming it does not change its provenance.

There are then two independent missing inputs.  First,
`property-t-free-el20-full-mf-radical`, followed by the internal rank transfer
`EL_20(R) ~= EL_12(R)`, would recover the headline without its Property-`(T)`
clause: full MF radical, trivial maps to MF groups, a countable non-MF group,
and a separable stably finite non-MF reduced group C-star algebra.  Second,
`property-t-free-torsion-free-full-mf-radical` must recover the torsion-free
main theorem without its Property-`(T)` clause.  The current torsion-free proof
uses Property `(T)` independently and is not a consequence of the Leavitt
collapse.

After both inputs are proved, the TeX rewrite may retain the no-`(T)` algebra
listed above and the two replacement theorems, while deleting the
Kazhdan-specific numbered block and explicit Property-`(T)` conclusions.
Historical prose which is not used by a retained numbered theorem may be
quarantined or removed; it is not a proof dependency.

The same boundary applies to Lean.  `Unconditional.lean` must import clean
modules containing actual unconditional proofs of both inputs.  It may not
import or quantify over `HasKazhdanPropertyT`, `NormalKazhdan`,
`KazhdanTransport`, a printed compression criterion, or a caller-supplied
literature premise.  Merely restating either missing input as an assumption
does not make the endpoint unconditional.
