import Mathlib.Tactic.Group
import GroupApproximation.Sofic.AscendingHNNCosetActionSofic
import GroupApproximation.Sofic.AscendingHNNWreathSofic
import GroupApproximation.Sofic.AscendingHNNProfiniteClosure
import GroupApproximation.Sofic.SoficActionChabauty

/-!
# A separable-base criterion, and its exact limitation

The transitive sofic-action criterion below is formally useful: if the level-zero
base copy `B = range (iotaVertical α hα)` is subgroup-separable inside the
ascending HNN extension, then the coset action `G ↷ G/B` is sofic.  The proof
is the general Chabauty/separability criterion for transitive actions.

The new file `AscendingHNNProfiniteClosure` determines exactly when this
hypothesis can occur.  It proves

`profiniteClosure B = ker (height α hα)`

and consequently

`B is subgroup-separable in G ↔ α is surjective`.

Thus for a **proper** injective self-embedding the separable-base hypothesis is
never satisfied: every finite-index subgroup of the HNN group containing `B`
already contains the whole height-zero mapping-telescope kernel.  In particular,
this route does not address Fournier-Facio's infinite-index question; it is a
positive control for the automorphic case and a useful warning that finite
quotients of the ambient HNN group cannot distinguish the strict compression.

The theorem `separable_range_of_separable_base` below remains a valid descent
statement, but in the proper case its premise is now known to be impossible.
-/
namespace GroupApproximation
namespace MarkedCompression

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- **The general separability criterion.**  If the base copy of `Γ` is a
separable subgroup of the ascending HNN extension -- every element outside it
is excluded by some finite-index subgroup containing it -- then the coset
action is sofic.

For a proper self-embedding this hypothesis is impossible by
`ascendingHNNBaseSeparable_iff_surjective`; the theorem is retained because it
is the exact transitive separability implication and a useful positive control. -/
theorem isSoficAction_vertical_cosets_of_separable_base
    (hsep : ∀ g : Vertical α hα, g ∉ (iotaVertical α hα).range →
      ∃ K : Subgroup (Vertical α hα),
        (iotaVertical α hα).range ≤ K ∧ K.FiniteIndex ∧ g ∉ K) :
    IsSoficAction (Vertical α hα) (Cosets α hα) :=
  isSoficAction_quotient_of_separable (iotaVertical α hα).range hsep

include hα in
/-- The separability hypothesis used by the preceding criterion forces `α` to
be onto.  Hence it has no proper ascending-HNN instances. -/
theorem surjective_of_separable_base_hypothesis
    (hsep : ∀ g : Vertical α hα, g ∉ (iotaVertical α hα).range →
      ∃ K : Subgroup (Vertical α hα),
        (iotaVertical α hα).range ≤ K ∧ K.FiniteIndex ∧ g ∉ K) :
    Function.Surjective α :=
  surjective_of_ascendingHNNBaseSeparable α hα hsep

/-- Conjugation by the inverse stable letter, as a homomorphism out of the
base copy.  It carries `α(Γ)` back onto the base and moves everything else off
it, which is what turns a finite-index subgroup of `G` into one of `Γ`. -/
def conjBase : Γ →* Vertical α hα where
  toFun x := (tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    group

@[simp] theorem conjBase_apply (x : Γ) :
    conjBase α hα x
      = (tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα := rfl

include hα in
/-- **The hypothesis descends to the base, so the reduction is not one-way.**

If the base copy is separable in `G`, then `α(Γ)` is separable in `Γ`.  This is
the first level of the tower described above, obtained rather than assumed, and
it makes the criterion testable: a base for which `α(Γ)` fails to be separable
cannot have its copy separable in `G`, so this route to soficity is unavailable
there and no search for a finite-index subgroup of `G` will help.

The proof is the computation behind the tower.  Conjugation by `t⁻¹` is a
homomorphism `φ : Γ → G` carrying `α(Γ)` into the base copy, since
`t⁻¹ ι(α y) t = ι(y)`, and carrying `γ` outside it exactly when `γ ∉ α(Γ)`.
Pulling a finite-index subgroup of `G` back along `φ` therefore produces a
finite-index subgroup of `Γ` containing `α(Γ)` and missing `γ`. -/
theorem separable_range_of_separable_base
    (hsep : ∀ g : Vertical α hα, g ∉ (iotaVertical α hα).range →
      ∃ K : Subgroup (Vertical α hα),
        (iotaVertical α hα).range ≤ K ∧ K.FiniteIndex ∧ g ∉ K)
    (γ : Γ) (hγ : γ ∉ α.range) :
    ∃ M : Subgroup Γ, α.range ≤ M ∧ M.FiniteIndex ∧ γ ∉ M := by
  classical
  have hγset : γ ∉ Set.range α := fun h => hγ (MonoidHom.mem_range.mpr h)
  have hout : conjBase α hα γ ∉ (iotaVertical α hα).range := by
    rw [conjBase_apply]
    exact tVertical_inv_conj_not_mem α hα hγset
  obtain ⟨K, hKle, hKfi, hKnot⟩ := hsep _ hout
  haveI := hKfi
  refine ⟨K.comap (conjBase α hα), ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_comap.mpr (hKle ⟨y, ?_⟩)
    rw [conjBase_apply, ← vertical_compress α hα y]
    group
  · refine ⟨?_⟩
    rw [Subgroup.index_comap]
    exact (Subgroup.instFiniteIndex_subgroupOf K (conjBase α hα).range).index_ne_zero
  · exact fun hmem => hKnot (Subgroup.mem_comap.mp hmem)

end MarkedCompression

namespace AscendingHNNWreath

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- The wreath product over the coset space is sofic for any sofic lamp
whenever the separable-base hypothesis holds.  By
`ascendingHNNBaseSeparable_iff_surjective`, this criterion applies only in the
automorphic case; it is retained as the direct wreath-product consequence of
the general transitive separability theorem. -/
theorem isSofic_wreath_cosets_of_separable_base {K : Type} [Group K]
    (hΓ : IsSofic Γ) (hK : IsSofic K)
    (hsep : ∀ g : MarkedCompression.Vertical α hα,
        g ∉ (MarkedCompression.iotaVertical α hα).range →
      ∃ L : Subgroup (MarkedCompression.Vertical α hα),
        (MarkedCompression.iotaVertical α hα).range ≤ L ∧ L.FiniteIndex ∧ g ∉ L) :
    IsSofic (Wreath K (MarkedCompression.Vertical α hα)
      (MarkedCompression.Cosets α hα)) :=
  GeneralizedWreath.isSofic_wreath hK (isSofic_vertical α hα hΓ)
    (MarkedCompression.isSoficAction_vertical_cosets_of_separable_base α hα hsep)

end AscendingHNNWreath

end GroupApproximation
