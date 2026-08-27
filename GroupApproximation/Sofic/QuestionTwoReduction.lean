import GroupApproximation.Sofic.CoronaImageNormalKazhdan
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Kazhdan.ShalomFinitePresentation

/-!
# The normal-Kazhdan reduction used by the torsion-free construction

This module proves the analytic reduction formerly recorded as proof-ledger
row `LI.14`:

> what remains is group-theoretic: a torsion-free finitely presented group
> whose subgroup `N_conj` contains a nontrivial normal property-`(T)`
> subgroup.

The reduction is a theorem.  It is provable from what the development already
has:
`CoronaImageNormalKazhdan.nk_05_assembly` kills a normal property-`(T)`
subgroup of the compression defect under every corona representation, and a
nontrivial element killed by every corona representation is exactly the
obstruction to being operator-MF.

`not_isOperatorMF_of_nontrivial_normal_kazhdan_defect` is that reduction.
Nothing here constructs a group satisfying the hypothesis.  The manuscript now
supplies that group-theoretic input at paper level from Fournier-Facio, Hull,
and Osin; that small-cancellation construction is not formalized in Lean.

## Why `nontrivial` is load-bearing

The ledger note for this row records that the print no longer explains the
emphasis, and that the row grading the explanation was deleted with the
sentence.  `obstruction_vacuous_at_bot` restores it: the trivial subgroup
satisfies every other hypothesis --- it is normal, it is contained in the
defect, and it has property `(T)` vacuously by
`Shalom.hasKazhdanPropertyT_of_subsingleton` --- and the conclusion the
obstruction then delivers is `⊥ ≤ Theta.ker`, which is `bot_le` and
constrains no representation whatsoever.  So the hypothesis without
nontriviality is satisfied by every compression datum and yields nothing.

## Manuscript status

This is the Lean-verified final implication used in the manuscript's
torsion-free consequence.  It must not be described as a Lean proof of the
paper-level small-cancellation construction.
-/

namespace GroupApproximation
namespace QuestionTwoReduction

open CoronaImageNormalKazhdan

variable {G : Type u} [Group G]

/-! ## A nontrivial invisible element is the whole obstruction -/

/-- An element that every corona representation sends to `1`, and that is not
itself `1`, forbids operator-MF: an injective representation would have to
separate it from the identity. -/
theorem not_isOperatorMF_of_nontrivial_invisible {x : G} (hx : x ≠ 1)
    (hinv : CoronaMFInvisible x) : ¬ IsOperatorMF G := by
  rintro ⟨X, hX, rho, hrho⟩
  exact hx (hrho (by rw [hinv X hX rho, map_one]))

/-! ## The reduction -/

variable {Gamma H : Type} [Group Gamma] [Group H]

/-- Every element of a normal property-`(T)` subgroup of the compression
defect is invisible to every corona representation.  This is
`nk_05_assembly` read through the equivalence between the unitary-sequence
corona and the unitary group of the C⋆-corona. -/
theorem coronaMFInvisible_of_mem_normal_kazhdan_defect [Countable H]
    (C : KazhdanCompressionCore Gamma H) (K : Subgroup H) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K) (hK : K ≤ C.defectNormal)
    {k : H} (hk : k ∈ K) : CoronaMFInvisible k := by
  intro X hX rho
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  -- the printed `Theta`, obtained from `rho` through the canonical equivalence
  set Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho with hTheta
  have hker : K ≤ Theta.ker := nk_05_assembly C K hT hK X hX Theta
  have h1 : Theta k = 1 := MonoidHom.mem_ker.mp (hker hk)
  have h2 : (normMatrixCoronaUnitaryEquiv X) (rho k) = 1 := h1
  have h3 : (normMatrixCoronaUnitaryEquiv X) (rho k)
      = (normMatrixCoronaUnitaryEquiv X) 1 := by
    rw [h2, map_one]
  exact (normMatrixCoronaUnitaryEquiv X).injective h3

/-- **The normal-Kazhdan reduction.**  A countable group carrying a compression datum
whose defect contains a *nontrivial* normal property-`(T)` subgroup is not
operator-MF.

This is an obstruction theorem, not an existence theorem.  The manuscript's
existence argument is paper-level, and nothing here formalizes it. -/
theorem not_isOperatorMF_of_nontrivial_normal_kazhdan_defect [Countable H]
    (C : KazhdanCompressionCore Gamma H) (K : Subgroup H) [K.Normal]
    (hT : HasKazhdanPropertyT.{0, 0} K) (hK : K ≤ C.defectNormal)
    (hne : K ≠ ⊥) : ¬ IsOperatorMF H := by
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine not_isOperatorMF_of_nontrivial_invisible (x := (k : H)) ?_ ?_
  · exact fun hcon ↦ hk1 (Subtype.ext hcon)
  · exact coronaMFInvisible_of_mem_normal_kazhdan_defect C K hT hK k.2

/-! ## Why the nontriviality is load-bearing -/

/-- The trivial subgroup satisfies every hypothesis of the obstruction except
nontriviality: it is normal, it lies in the defect, and it has property
`(T)` vacuously. -/
theorem bot_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (⊥ : Subgroup H) :=
  Shalom.hasKazhdanPropertyT_of_subsingleton

/-- **And the conclusion it delivers is empty.**  At `K = ⊥` the obstruction
reads `⊥ ≤ Theta.ker`, which holds of every homomorphism whatsoever, so it
constrains no representation and forbids nothing.  That is the reason the
printed sentence says *nontrivial*. -/
theorem obstruction_vacuous_at_bot
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
    (⊥ : Subgroup H) ≤ Theta.ker :=
  bot_le

end QuestionTwoReduction
end GroupApproximation
