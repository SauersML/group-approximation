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
| `QuantitativeCollapse.lean` | the three printed endpoints |

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
