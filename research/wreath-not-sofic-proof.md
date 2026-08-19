---
rg: 2
id: wreath-not-sofic-proof
kind: route
title: Identification of the candidate with Kun–Thom's Theorem E pair
target: wreath-not-sofic
requires: [kun-thom-nonsofic-wreath]
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Identification of the candidate with Kun–Thom's Theorem E pair

The external theorem lives in `kun-thom-nonsofic-wreath`, which holds Theorems
A, C, E and Corollary D verbatim with their own trust paragraph. This route
does not restate them. It does the one thing a citation cannot do for itself:
check that *this* graph's candidate is literally a group Theorem A covers.

## The two gaps, and why they were unclosable before

The scout left this node open on two identification gaps — the lamp group
(`ℤ/2ℤ` in Theorem A, possibly `ℤ` for us) and whether our pair is
infranormal, non-normal and Kazhdan on both sides. Neither could be closed as
posed, because "the wreath candidate" had never been bound to a group. A
full-corpus grep finds the phrase outside `research/` in exactly two places:
`notes/OBSTRUCTIONS.md:123`, which uses it substantively but never defines it,
and `notes/NOTEPAD.md:31454`, which is a *different* object — the split
integral wreath candidate. Everything else is downstream restatement. The
symbol was free.

## The binding

It is bound in `wreath-not-sofic` to Kun–Thom's Theorem E pair, which is the
reading the whole `notes/` corpus already uses: `notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md`
fixes `q = 2`, `r,d ≥ 3`, `Γ = EL_r(R₊)`, `G = EL_r(R) ⋊ SL_d(ℤ)`;
`notes/COMMUTING_WREATH_SOFIC_RADICAL.md` and `notes/PERFECT_CORE_KUN_THOM_WREATH.md`
write the candidate as `W = (⊕_{G/Γ} C₂) ⋊ G` and call it the Kun–Thom group;
`notes/OBSTRUCTIONS.md` §3–§4 uses the matching notation (`e_{ij}(x^v)`,
"compressors come from `SL_d(ℤ)` monomial substitutions"). The archivist's
sweep confirms the corpus asserts nonsoficity of that group about six times as
a Kun–Thom citation, and that no `notes/` file states the identification — which
is precisely why it had to be made here rather than found.

With the binding in place both gaps close by inspection, not by argument:

1. **Lamp group.** `ℤ/2ℤ`. The scout's caution is correct and is preserved in
   `wreath-not-sofic` as a scope boundary: the split integral candidate
   `W_Y = ℤ^{(Y)} ⋊ Q` has `ℤ` lamps over `Q/Γ` for the amalgam `Q = G *_N G`,
   and nonsoficity does not pass along the lamp surjection `ℤ ↠ ℤ/2ℤ` in the
   needed direction. That group is a different node and is **not** covered.
2. **The pair.** Theorem E's own pair, so Theorem E supplies infranormality,
   non-normality and property (T) on both sides directly.

Nothing downstream needs `ℤ` lamps. `flexible-side-witness`,
`hyperlinear-wreath-model`, `growing-fiber-models` and the rigidity route all
read the candidate as the `ℤ/2ℤ` Bernoulli crossed product
`M_KT = L^∞({±1}^{G/Γ}) ⋊ G`, so the binding is free rather than a
restriction — the swap the coordinator asked me to evaluate costs nothing.

## Corpus check for an existing proof

Route (i) — an in-repo proof — is not available, and this was verified rather
than assumed. Every unconditional `¬ IsSofic` theorem under
`GroupApproximation/` is about elementary, GL or unit groups over Leavitt
algebras: `Endpoint/MainResults.universalLeavittEL4_not_isSofic` at
`EL₄(L_{𝔽₂}(1,2))`, its rank and arity variants, and the general form
`Leavitt/GeneralCornerTheorem.corner_not_isSofic` at `EL_{m+1}(R)`. The
criterion behind them, `Criterion/CriterionAssembly.not_isSofic_of_not_isLEF`,
needs a `CompressionSetup G Γ J` plus (T) at both `G` and `Γ` plus a non-LEF
commuting witness `J`, and is instantiated nowhere near a wreath product. The
wreath material in Lean (`Sofic/MonomialModel.wreathPerm` and its metric
lemmas) is finite-model gadgetry; `Sofic/CoordinateTransfer.lean` and
`Sofic/ImplementerCocycle.lean` are explicit no-gos about routes and say in
their own docstrings that they do not bear on the wreath product's status. The
archivist's independent sweep reaches the same conclusion: "Lean has an
interface but no inhabitant."

So the establishment is by citation, and the trust surface is exactly the one
recorded in `kun-thom-nonsofic-wreath` — one unrefereed preprint, statements
read but proofs not audited — inherited here unchanged.
