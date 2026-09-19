---
rg: 2
id: mf-implies-hyperlinear
kind: claim
title: MF implies hyperlinear under the weak norm-corona convention
root: true
distinct_from:
  hyperlinear-not-imply-mf: That established claim refutes the reverse implication; this claim asks whether norm-corona MF groups always admit faithful Hilbert--Schmidt models.
  sofic-implies-hyperlinear: Soficity supplies canonical traces through permutation models; a weak MF corona embedding need not make its coordinate traces faithful.
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
---

Every MF group in the Carrión--Dadarlat--Eckhardt norm-matrix-corona sense is
hyperlinear.

Operator-norm multiplicativity controls normalized Hilbert--Schmidt defect,
but the defining MF embedding alone does not ensure faithful coordinate
traces, so the implication is not formal from the definitions.

## Ideas

**What the gap is.**  Operator-norm separation of `g` is a rank-one
phenomenon: `||phi_n(g)-1||_op >= 1` only forces the trace gap
`1-Re tr(phi_n(g)) >= 1/(2d_n)`.  Hyperlinearity needs that gap bounded
below.  So the claim is exactly the assertion that operator-visible elements
can always be made *macroscopically* visible.

**No model-by-model proof can exist.**  This is established, and formalized:
`weak-mf-embedding-not-reusable`.  Identity-block padding preserves every
operator-norm distance and dilutes every Hilbert--Schmidt quantity by the
relative dimension (`NormTraceGap`), the irrational-rotation representations
of `Z` do the same with no multiplicative defect at all, and amplification
drives distance to the scalars rather than deviation rank.  So any proof must
select models and any refutation must rule out all of them.

**The reduction is formalized.**  `NormTraceGap.isHyperlinear_of_traced_normModels`
already converts operator-norm models with separating traces into hyperlinear
models: the trace clause is the entire remaining content.  What
`hyperlinear-elementwise-visibility` adds is that an arbitrarily small trace
gap, one element at a time, suffices.

**Elementwise reformulation.**  By `hyperlinear-elementwise-visibility` the
claim is equivalent to the elementwise inclusion of residuals
`Rad_hyp(G) <= Rad_MF(G)` for every group, i.e. every MF-visible element is
tracially visible.  Note `mf-hyperlinear-radical-divergence` establishes the
*opposite* non-inclusion for one explicit word, which is consistent and shows
the two radicals are genuinely different objects.

**Established fragments.**  `mf-finite-normal-tracially-visible` (finite
normal subgroups), `mf-hyperlinear-of-finite-normal-quotient` (=
arXiv:2508.17392v3, Proposition 1.6), and the structure of any counterexample
in `mf-nonhyperlinear-collapse-structure`: its hyperlinear residual is
infinite and contains no finite normal subgroup.  The torsion-central
mechanism which produces the non-MF theorems therefore cannot be recycled.

**Two live mechanisms, one constant.**  Amplification
(`mf-implies-hyperlinear-via-rank-profile`) and invariant corners
(`mf-implies-hyperlinear-via-invariant-corner`).  By
`corner-renormalization-cost` both are governed by `sqrt(d/r)`; a functor
pays it in the defect, a corner pays it structurally.

**Dead ends already recorded.**  Raw tensor powers accumulate a scalar phase
and can return the trace to `1`; direct sums dilute one summand's visibility
by the number of summands; and no continuous homomorphism `U(d)->U(N)` beats
the `sqrt(d)` loss (`FALSE_FERMIONIC_AMPLIFICATION.md`, Theorem 5).  A proof
must therefore use the group, not the matrices.

**Cost of the negative branch.**  `mf-refutation-yields-nonhyperlinear-group`:
a counterexample is a nonhyperlinear group, so refutation is at least as hard
as the program's primary target.

**The trace-level dictionary.**  Four statements, only one of which is open:

```text
MF trace  => hyperlinear trace          trivial (||.||_2 <= ||.||)
hyperlinear trace => MF trace           REFUTED: hyperlinear-trace-not-mf-trace
hyperlinear group => MF group           REFUTED: hyperlinear-not-imply-mf
MF group  => hyperlinear group          THIS CLAIM
```

The asymmetry is instructive.  At trace level the easy direction is the
norm-to-trace one, because a trace is given; at group level the easy
direction is the reverse, because a group model carries separation but no
trace.  What this root asks for is exactly the missing trace.

**Literature status (swept 2026-08-14).**  No general converter is recorded.
Bachner--Dogon--Lubotzky, arXiv:2508.17392v3, prove only the finite-normal
kernel converters (Propositions 1.6 and 1.7) and the Deligne-type
stability statement (Proposition 1.5); their abstract still calls "whether
all groups are MF" a longstanding open problem.  Quasidiagonality of the
*reduced* group C-star algebra implies amenability (Rosenberg, appendix to
Hadwin, *Strongly quasidiagonal C-star algebras*, J. Operator Theory 18
(1987) 3--18) and hence hyperlinearity, but that hypothesis is far stronger
than the weak norm-corona convention used here and gives nothing for it.
