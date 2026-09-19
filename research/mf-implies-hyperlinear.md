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
  - research/artifacts/mf-hyperlinear-frontier-2026-08-19.md
---

Every MF group in the Carrión--Dadarlat--Eckhardt norm-matrix-corona sense is
hyperlinear.

Operator-norm multiplicativity controls normalized Hilbert--Schmidt defect,
but the defining MF embedding alone does not ensure faithful coordinate
traces, so the implication is not formal from the definitions.

## Ideas

**What the gap is.**  Operator-norm separation of `g` is a rank-one
phenomenon: `||phi_n(g)-1||_op >= 1` only forces the trace gap
`1-Re tr(phi_n(g)) >= 1/(2d_n)`.  Hyperlinearity needs that gap bounded below.
So the claim is exactly the assertion that operator-visible elements can
always be made *macroscopically* visible.

**No model-by-model proof can exist.**  This is established and formalized:
`weak-mf-embedding-not-reusable`.  Identity-block padding preserves every
operator-norm distance and dilutes every Hilbert--Schmidt quantity by relative
dimension (`NormTraceGap`); irrational-rotation representations of `Z` do the
same with no multiplicative defect; and amplification drives distance to the
scalars rather than deviation rank.  Any proof must select models and any
refutation must rule out all of them.

**The reduction is formalized.**  `NormTraceGap.isHyperlinear_of_traced_normModels`
converts operator-norm models with separating traces into hyperlinear models.
`hyperlinear-elementwise-visibility` sharpens this: an arbitrarily small
positive trace gap, one element at a time, suffices.

**Elementwise reformulation.**  The claim is equivalent to the residual
inclusion `Rad_hyp(G)<=Rad_MF(G)` for every group: every MF-visible element is
tracially visible.  `mf-hyperlinear-radical-divergence` establishes the
opposite non-inclusion for one explicit word, consistently showing that the
two radicals are genuinely different objects.

**Kernel-checked Kazhdan fragment (2026-08-19).**  The established Cairn claim
`kazhdan-mf-hyperlinear-fragment` records two closed theorems from
`Sofic/KazhdanCorner.lean`: every nontrivial property-(T) weak-MF group has a
nontrivial hyperlinear quotient, and every nontrivial simple property-(T)
weak-MF group is hyperlinear.  This does not close the root: the quotient can
have nontrivial kernel for a nonsimple source, and the audited Kazhdan-envelope
shortcut uses quotient operations that do not preserve weak MF.

**Exact frontier after the August 19 pass.**  The two surviving mechanisms are
still `mf-trace-gap-defect-ratio-models` and the stronger
`mf-invariant-corner-visibility`.  The first asks for models with
`epsilon_n^2/kappa_n -> 0`; the second asks to make each MF-visible element
macroscopically visible on an invariant renormalized corner.  Universal
post-processing is not a substitute: `FALSE_FERMIONIC_AMPLIFICATION.md`
proves the square-root Lipschitz cost, and padding proves the complementary
model-level no-go.  See `research/artifacts/mf-hyperlinear-frontier-2026-08-19.md`.

**Established fragments.**  `mf-finite-normal-tracially-visible` (finite
normal subgroups), `mf-hyperlinear-of-finite-normal-quotient` (=
arXiv:2508.17392v3, Proposition 1.6), and the structure of any counterexample
in `mf-nonhyperlinear-collapse-structure`: its hyperlinear residual is
infinite and contains no finite normal subgroup.  The torsion-central
mechanism producing the non-MF theorems therefore cannot be recycled.

**Two live mechanisms, one constant.**  Amplification
(`mf-implies-hyperlinear-via-rank-profile`) and invariant corners
(`mf-implies-hyperlinear-via-invariant-corner`).  By
`corner-renormalization-cost` both are governed by `sqrt(d/r)`; a functor pays
it in the defect, a corner pays it structurally.

**Dead ends already recorded.**  Raw tensor powers accumulate a scalar phase
and can return the trace to `1`; direct sums dilute one summand's visibility;
and no continuous homomorphism `U(d)->U(N)` beats the `sqrt(d)` loss
(`FALSE_FERMIONIC_AMPLIFICATION.md`, Theorem 5).  A proof must therefore use
the group, not the matrices.

**Cost of the negative branch.**  `mf-refutation-yields-nonhyperlinear-group`:
a counterexample is a nonhyperlinear group, so refutation is at least as hard
as the program's primary target.

**The trace-level dictionary.**  Four statements, only one open:

```text
MF trace  => hyperlinear trace          trivial (||.||_2 <= ||.||)
hyperlinear trace => MF trace           REFUTED: hyperlinear-trace-not-mf-trace
hyperlinear group => MF group           REFUTED: hyperlinear-not-imply-mf
MF group  => hyperlinear group          THIS CLAIM
```

The asymmetry is instructive.  At trace level the easy direction is the
norm-to-trace one because a trace is given; at group level the easy direction
is the reverse because a group model carries separation but no trace.  This
root asks for exactly the missing trace.

**Literature status (swept 2026-08-14).**  No general converter is recorded.
Bachner--Dogon--Lubotzky, arXiv:2508.17392v3, prove only the finite-normal
kernel converters (Propositions 1.6 and 1.7) and the Deligne-type stability
statement (Proposition 1.5).  Quasidiagonality of the reduced group C-star
algebra implies amenability and hence hyperlinearity, but that hypothesis is
far stronger than the weak norm-corona convention used here.
