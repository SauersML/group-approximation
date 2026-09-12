# Lane `quant-collapse` — `prop:linear-collapse`

Carries Proposition `prop:linear-collapse` of `non_mf_groups_exist.tex` (the
section "A finite certificate") and the two unlabelled consequences printed
after its proof: a full MF radical is equivalent, for a marked group, to a
*finite, checkable inequality* about tuples of unitary matrices.

The files and the namespace are still called `QuantitativeCollapse`, from the
working title; only the printed Props are named after the label.

## Statement as landed

```lean
def CollapseInequality (m : ℕ) (s : Finset (FreeGroup (Fin m))) (C : ℝ) : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ (U : Fin m → Matrix.unitaryGroup (Fin d) ℂ) (δ : ℝ),
    (∀ r ∈ s, ‖((FreeGroup.lift U r : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) - 1‖ ≤ δ) →
      ∀ i, ‖((U i : Matrix (Fin d) (Fin d) ℂ)) - 1‖ ≤ C * δ
```

The printed `max_j ‖r_j(U) - 1‖` is carried by the bound variable `δ`.  The
readings agree, `δ` avoids a nonemptiness side condition on `Finset.sup'`, and
it is the form the converse consumes.  `CollapseInequality` mentions the words
and the constant but not the group; that is exactly what makes the finitely
presented cover work.

Printed endpoints, all in
`GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapse`:

| Prop | theorem |
| --- | --- |
| `PrintedLinearCollapse` | `manuscriptLinearCollapse` |
| `PrintedLinearCollapseConverse` | `manuscriptLinearCollapseConverse` |
| `PrintedLinearCollapseCover` | `manuscriptLinearCollapseCover` |
| `PrintedLinearCollapseMarkedGroups` | `manuscriptLinearCollapseMarkedGroups` |

The converse carries `[Countable G]` exactly as printed, and countability is
load-bearing: the converse proves `manuscriptCoronaMFResidual G = ⊤` (that half
needs no countability and is exposed as
`manuscriptCoronaMFResidual_eq_top_of_collapseInequality`) and then applies
`manuscriptFullRadicalKillsMFTargets`, which is `prop:mf-residual-calculus`.

`PrintedLinearCollapseMarkedGroups` says the same finite family works for every
countable `m`-marked group satisfying it.  That is the content of the printed
openness sentence; the topology on the space of marked groups is **not**
formalized and no openness claim is made.

## Modules

| path | contents |
| --- | --- |
| `QuantitativeCollapseEstimates.lean` | step (iii): the two unitary estimates, the word budget, inequality (1) |
| `QuantitativeCollapsePerfect.lean` | steps (i) and (ii): perfectness, commutator words |
| `QuantitativeCollapseCorona.lean` | step (iv) analytic half: the corona homomorphism |
| `QuantitativeCollapse.lean` | the four printed endpoints |
| `QuantitativeCollapseSentences.lean` | the printed proof, one lemma per sentence |

## Proof route, and where each hypothesis is spent

1. **Perfectness.**  If `G` were not perfect its abelianization would be a
   nontrivial finitely generated abelian group.  Such a group has a nontrivial
   *finite* quotient, read off `CommGroup.equiv_free_prod_prod_multiplicative_zmod`:
   a free coordinate `z ≠ 0` survives in `ZMod (|z| + 1)`, a torsion coordinate
   is already finite and nontrivial.  Finite groups are MF
   (`isOperatorMF_of_finite_standard`), so the hypothesis is contradicted.
2. **Commutator words.**  Perfectness plus surjectivity of `FreeGroup.lift g`
   writes each generator as a product of commutators of *words*, giving the
   relations `w i = x_i⁻¹ ∏_k ⁅a_{ik}, b_{ik}⁆`.
3. **`eq:bootstrap`.**  `‖AB - 1‖ ≤ ‖A-1‖ + ‖B-1‖` and
   `‖⁅A,B⁆ - 1‖ ≤ 2‖A-1‖‖B-1‖` give `D(U) ≤ δ + B·D(U)²` with `B` depending
   only on the chosen words.
4. **The contradiction.**  If no finite family and constant worked, pick for
   each `n` a counterexample against the first `n` relations of an exhaustion,
   with constant `n+1`.  Then `δ_n → 0`, the tuples define a corona
   homomorphism, the hypothesis kills it, so `D(U⁽ⁿ⁾) → 0`; but (1) gives
   `1 < 1/(n+1) + B·D(U⁽ⁿ⁾)` for every `n`.  Positivity of the matrix size is
   not assumed: the counterexample is taken against `d ≥ 1` because that is what
   the printed inequality quantifies over.

The converse lifts the images of the generators to unitary sequences, notes
that relation defects vanish, and applies the inequality with a shrinking `δ`.
The corollary applies the converse to `PresentedGroup ↑s` with the same words.

## The printed proof, sentence by sentence

`QuantitativeCollapseSentences.lean` carries the proof of
`prop:linear-collapse` and the consequence paragraph after it, one
`manuscriptSentence_*` lemma per printed sentence, all in namespace
`GroupApproximation.Manuscript.OneSidedMFRadical.QuantitativeCollapseSentences`
and each proved from the four modules above.

| printed sentence | lemma |
| --- | --- |
| a nontrivial abelianization of a finitely generated group has a nontrivial finite quotient | `manuscriptSentence_fgAbelianHasFiniteQuotient` |
| and finite groups are MF | `manuscriptSentence_finiteGroupsAreMF` |
| The group `G` is perfect | `manuscriptSentence_perfect` |
| So there are words `a_ik, b_ik ∈ F_m` with `g_i = ∏_k [a_ik(g), b_ik(g)]` | `manuscriptSentence_generatorsAreCommutatorProducts` |
| and the words `w_i = x_i⁻¹ ∏_k [a_ik, b_ik]` are relations of `G` | `manuscriptSentence_relatorWords` |
| For a tuple `U` of unitaries put `D(U) = max_i ‖U_i - 1‖` | `manuscriptSentence_generatorDefect` |
| A word `a` of length `|a|` has `‖a(U) - 1‖ ≤ |a| D(U)` | `manuscriptSentence_wordLengthBound` |
| and unitaries `A, B` satisfy `‖[A,B] - 1‖ = ‖AB - BA‖ ≤ 2‖A-1‖‖B-1‖` | `manuscriptSentence_commutatorEstimate` |
| since `AB - BA = (A-1)(B-1) - (B-1)(A-1)` | `manuscriptSentence_commutatorIdentity` |
| So there is a constant `B₀`, determined by the chosen words, with `eq:bootstrap` | `manuscriptSentence_bootstrap` |
| Enumerate the relations of `G` as `r₁, r₂, …` with `w₁,…,w_m` first, and put `R_n` | `manuscriptSentence_relationEnumeration` |
| If no `R_n` works with the constant `n`, there are `d_n` and tuples `U⁽ⁿ⁾` with `D(U⁽ⁿ⁾) > n δ_n` | `manuscriptSentence_counterexampleTuples` |
| Since `D(U⁽ⁿ⁾) ≤ 2` | `manuscriptSentence_defectBoundedByTwo` |
| …, `δ_n → 0` | `manuscriptSentence_relationDefectsVanish` |
| so `g_i ↦ [U_i⁽ⁿ⁾]_n` is a homomorphism from `G` to the unitary group of `∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)` | `manuscriptSentence_coronaHomomorphism` |
| trivial by hypothesis; so `D(U⁽ⁿ⁾) → 0` | `manuscriptSentence_generatorDefectsVanish` |
| For `n ≥ m`, `eq:bootstrap` gives …, and division by `D(U⁽ⁿ⁾)` gives `1 ≤ 1/n + B₀ D(U⁽ⁿ⁾)`, which fails for large `n` | `manuscriptSentence_bootstrapContradiction` |
| Conversely, a corona homomorphism has unitary coordinate lifts whose relation defects tend to zero | `manuscriptSentence_coronaLiftsHaveVanishingDefects` |
| so the displayed inequality forces every generator lift to the identity, and the homomorphism is trivial | `manuscriptSentence_inequalityKillsCorona` |
| Lemma `prop:mf-residual-calculus` extends this to every homomorphism to an MF group | `manuscriptSentence_residualCalculusExtends`, applied to `manuscriptSentence_inequalityGivesFullRadical` |
| With `r₁,…,r_s` as in the proposition, put `P = ⟨x₁,…,x_m | r₁,…,r_s⟩`; the inequality holds verbatim for `P`, so every such group is a quotient of a finitely presented group with the same property and the same number of generators | `manuscriptSentence_presentedCover` |
| The set of `m`-marked groups satisfying `r₁ = ⋯ = r_s = 1` … and every group in it has the property | `manuscriptSentence_markedGroupsSatisfyingRelations` |
| For the two-generated group `Q` of `thm:torsion-free` … | **not carried here**: needs Theorem 5, and belongs to lane `thm-e` |

Two carriers are deliberately not literal transcriptions, and say so in their
docstrings.  `manuscriptSentence_wordLengthBound` gives a constant produced by
the free-group induction rather than the length of a particular spelling, which
is all the printed argument uses.
`manuscriptSentence_markedGroupsSatisfyingRelations` carries only the middle
clause of its sentence: the space of marked groups and its topology are not
formalized anywhere in this development, so the printed words "open and closed"
are not claimed by any Lean statement.

The sentence carriers take printed hypotheses, so they are gated by
`#audit_axioms` rather than `#audit_closed_axioms`; the closed endpoints that
the stronger gate applies to stay in `QuantitativeCollapse.lean`.

## Gotchas recorded here

* Mathlib's commutator bracket `⁅a, b⁆` is a **scoped** instance:
  `open scoped commutatorElement` is required, and without it the failure is
  `failed to synthesize Bracket G G` at every use site.
* `mul_inv_rev` is ambiguous under `open Matrix`; write `_root_.mul_inv_rev`.
* `Countable (FreeGroup α)` lives in `Mathlib.SetTheory.Cardinal.Free`.
* `opLength Y u` and the printed `‖U - 1‖` over `M_d(ℂ)` are definitionally
  equal at `Y = naturalFiniteModel d`; `collapseInequality_model` and
  `collapseInequality_of_model` pin both directions of that bridge.

## Status

See the git log for the landed commits; every endpoint carries an
`#audit_closed_axioms` line and all three pass.  Nothing in this lane is
conditional: no proof is left open and no hypothesis Prop is used as a stand-in
for one.
