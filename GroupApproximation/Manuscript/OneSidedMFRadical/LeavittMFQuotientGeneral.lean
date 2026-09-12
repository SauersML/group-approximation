import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCorollariesRankTwo
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Algebra.FinitelyGeneratedAbelianResiduallyFinite
import GroupApproximation.Leavitt.AryLeavitt
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:leavitt-mf-quotient` at every `d ≥ 2`

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`:

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let
> `H = R^×`.  Then `H ≅ GL_d(R)`, the intersection of the kernels of all
> homomorphisms from `H` to MF groups is `[H,H] = EL_d(R)`, and
> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`.

## The three-step chain

The printed proof runs `EL_d(R) ≤ ⋂_ρ ker ρ ≤ [H,H] ≤ EL_d(R)`:

* `EL_d(R) ≤ ⋂ ker ρ` is Theorem B at rank `d`, which this repository now
  proves for every `n ≥ 2` and every `L_k(1,m)`, so this step is
  unconditional;
* `⋂ ker ρ ≤ [H,H]` is the abelianization map, which is a homomorphism to a
  countable abelian group and so to an MF group — `isOperatorMF_of_commGroup_countable`
  of `Algebra.FinitelyGeneratedAbelianResiduallyFinite`;
* `[H,H] ≤ EL_d(R)` is the Khanh--Thanh decomposition `GL_d(R) = EL_d(R)D_d(k)`
  with `D_d(k)` abelian and normalizing, and it is the **only** literature
  input.  It appears here as the named proposition
  `PrintedKhanhThanhCommutatorInElementary`, in the weakest form the chain
  needs: not the decomposition itself, only its consequence that the
  commutator subgroup of `GL_d(R)` lies in `EL_d(R)`.

## What is and is not carried

`H ≅ GL_d(R)` is the printed module isomorphism `R ≅ M_d(R)`, which is
`CompleteMatrixFamily.unitsEquiv` at the `d`-ary Leavitt family — already in
the tree, for every `d`.

The identification of the quotient with `K₁(R)` and with `k^×/(k^×)^{d-1}` is
**not** carried here.  It is the second half of the same Khanh--Thanh citation, and
naming the quotient is not needed for any of the three inclusions; the
corollary's group-theoretic content is exactly `⋂ ker ρ = [H,H] = EL_d(R)`,
which is what `PrintedLeavittMFQuotientGeneral` states.  Both identifications
are proved elsewhere without the citation:
`LeavittMFQuotientSentences.manuscriptSentence_quotientByCommutatorIsKOne` with
`K₁(R)`, and `LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula` with
`k^×/(k^×)^{d-1}`.

At `d = 2` none of this is needed: `LeavittMFQuotient` proves the whole
corollary outright, because `K₁(L_k(1,2)) = 0` makes the quotient trivial, so
the Khanh--Thanh hypothesis below is discharged there rather than assumed.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace LeavittMFQuotientGeneral

open AryLeavitt

/-! ## `H ≅ GL_d(R)` -/

/-- **The printed module isomorphism**, in its unit-group form:
`R^× ≅ GL_d(R)` for `R = L_k(1,d)`. -/
noncomputable def unitsEquivGL (k : Type) [Field k] (d : ℕ) :
    (AryLeavittAlgebra k d)ˣ ≃*
      (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ :=
  ((AryLeavitt.family k d).unitsEquiv).symm

/-! ## The one literature input -/

/-- **The Khanh--Thanh input**, in the weakest form the printed chain uses.

Khanh--Thanh show `GL_d(R) = EL_d(R)D_d(k)` with `D_d(k)` the abelian group of
diagonal matrices over `k^×`, which normalizes `EL_d(R)`; the consequence used
below is only that the commutator subgroup of `GL_d(R)` lies in `EL_d(R)`.
Stating the consequence rather than the decomposition keeps the citation's
footprint to one inclusion. -/
def PrintedKhanhThanhCommutatorInElementary (k : Type) [Field k] (d : ℕ) :
    Prop :=
  commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
    ≤ elementaryGroup (Fin d) (AryLeavittAlgebra k d)

/-! ## The two unconditional inclusions -/

section Chain

variable (k : Type) [Field k] [Countable k] (d : ℕ)

/-- `Matrix` is a definition, not a `Pi` type as far as instance search is
concerned, so the countability of the matrix ring has to be handed over
explicitly. -/
instance countableAryMatrix :
    Countable (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) :=
  inferInstanceAs (Countable (Fin d → Fin d → AryLeavittAlgebra k d))

instance countableAryGL :
    Countable (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ :=
  Function.Injective.countable
    (f := (Units.val : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ →
      Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)))
    (fun _ _ h ↦ Units.ext h)

/-- **`EL_d(R) ≤ ker ρ` for every homomorphism to an MF group.**  This is
Theorem B at rank `d`, which the repository proves for every `n ≥ 2`. -/
theorem elementary_le_ker (hd : 2 ≤ d) (M : Type) [Group M]
    (hM : IsOperatorMF M)
    (f : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ →* M) :
    elementaryGroup (Fin d) (AryLeavittAlgebra k d) ≤ f.ker := by
  intro x hx
  exact FullDefectRingEJZUnconditional.manuscriptLeavittAlgebraFullDefectRankTwoAllCharacteristics
    k d hd d hd M hM
    (f.comp (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).subtype) ⟨x, hx⟩

end Chain

/-- **The intersection of the kernels lies in the commutator subgroup**, for
every countable group.  The abelianization map is a homomorphism to a countable
abelian group, and a countable abelian group is MF.

Stated for an arbitrary countable group rather than for `GL_d(R)`: nothing
about the Leavitt algebra enters, and the countability the proof needs is
countability of the group itself. -/
theorem mfKernels_le_commutator {G : Type} [Group G] [Countable G] {x : G}
    (hx : ∀ (M : Type) [Group M], IsOperatorMF M → ∀ (f : G →* M), f x = 1) :
    x ∈ commutator G := by
  haveI : Countable (Abelianization G) :=
    (QuotientGroup.mk'_surjective (commutator G)).countable
  have hMF : IsOperatorMF (Abelianization G) :=
    MFQuotientUnits.isOperatorMF_of_commGroup_countable _
  have hker : x ∈ (Abelianization.of : G →* Abelianization G).ker :=
    hx _ hMF Abelianization.of
  rwa [Abelianization.ker_of] at hker

/-! ## The printed corollary -/

/-- **`cor:leavitt-mf-quotient`, group-theoretic content, at every `d ≥ 2`.**

`H ≅ GL_d(R)`; the commutator subgroup of `GL_d(R)` is `EL_d(R)`; and an
element of `GL_d(R)` lies in `EL_d(R)` exactly when every homomorphism to an
MF group kills it.  Together these are `⋂_ρ ker ρ = [H,H] = EL_d(R)`.

The identification of the quotient with `K₁(R)` and `k^×/(k^×)^{d-1}` is the
other half of the Khanh--Thanh citation and is not asserted. -/
def PrintedLeavittMFQuotientGeneral : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    PrintedKhanhThanhCommutatorInElementary k d →
      Nonempty ((AryLeavittAlgebra k d)ˣ ≃*
          (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∧
        commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
            = elementaryGroup (Fin d) (AryLeavittAlgebra k d) ∧
        (∀ x : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
          x ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d) ↔
            ∀ (M : Type) [Group M], IsOperatorMF M →
              ∀ (f : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ →* M),
                f x = 1)

theorem manuscriptLeavittMFQuotientGeneral :
    PrintedLeavittMFQuotientGeneral := by
  intro k _ _ d hd hKT
  have hEL : ∀ x, x ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d) →
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ →* M),
          f x = 1 := by
    intro x hx M _ hM f
    exact elementary_le_ker k d hd M hM f hx
  have hcomm : commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
      = elementaryGroup (Fin d) (AryLeavittAlgebra k d) := by
    refine le_antisymm hKT ?_
    intro x hx
    exact mfKernels_le_commutator (fun M _ hM f ↦ hEL x hx M hM f)
  refine ⟨⟨unitsEquivGL k d⟩, hcomm, fun x ↦ ⟨fun hx M _ hM f ↦ hEL x hx M hM f,
    fun hx ↦ ?_⟩⟩
  have hxc := mfKernels_le_commutator hx
  rwa [hcomm] at hxc

end LeavittMFQuotientGeneral
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms
  LeavittMFQuotientGeneral.manuscriptLeavittMFQuotientGeneral
