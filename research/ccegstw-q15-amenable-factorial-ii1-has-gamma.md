---
rg: 2
id: ccegstw-q15-amenable-factorial-ii1-has-gamma
kind: claim
title: Every amenable type II_1 factorial tracially complete C*-algebra has property Gamma (CCEGSTW Question 1.5)
refuted_by: [amenable-factorial-ii1-tracially-complete-without-gamma]
distinct_from:
  nontrivial-w-star-bundle-with-r-fibres-exists: that is BBSTWW Question 3.14 about abstract R-fibre W*-bundles, with no amenability hypothesis; this is the tracially complete Connes question for amenable algebras with any designated trace set.
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that asks for uniform Gamma of simple nuclear C*-algebras; by CCEGSTW Proposition 5.20 its completions are instances of this question.
---

**The question.** CCEGSTW, arXiv:2310.20594v6 (7 Aug 2026), Question 1.5, verbatim: "Does every
amenable type II1 factorial tracially complete C∗-algebra satisfy property Γ?"
- CCEGSTW call it fundamental: through [CETW, Theorem 5.6], a positive answer would resolve
  Toms–Winter.
- Their regularity table lists the class "Amenable factorial II1 tracially complete C∗-algebra" as
  "Open".
- Known positive cases: `∂_e X` compact and zero-dimensional (their Proposition 5.28), and, as
  announced there, compact and finite-dimensional.

**REFUTED (2026-09-13, unreviewed)** by `amenable-factorial-ii1-tracially-complete-without-gamma`.
- **Poulsen designated traces.** Toms's simple nuclear AH algebra without uniform Γ
  (`toms-ah-counterexample-to-uniform-gamma`, arXiv:2606.12188v2, Theorem 5) already gives a negative
  answer through CCEGSTW Proposition 5.20. CCEGSTW v6 does not cite Toms's paper.
- **Bauer designated traces.** The Pauli tower completion
  (`amenable-bauer-factorial-tracially-complete-without-gamma`) has a Bauer designated trace set. It
  fails Γ in the strongest form: its reduced power has no projection of constant trace `1/2`, central
  or not.
- **What survives.**
  - Γ from strict comparison, which is Toms–Winter itself.
  - Γ from a Winter-type tracial divisibility hypothesis, CCEGSTW's "modified Toms–Winter" variant.
    The Pauli completion fails tracial divisibility, so it does not bear on this variant.
