import GroupApproximation.PropertyT.EJZIntegralReduction
import GroupApproximation.PropertyT.A2MagicExponentFree
import GroupApproximation.PropertyT.IntegralCharacterMass
import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Steinberg.HigherRankFiniteControl
import GroupApproximation.Meta.AxiomGuard

/-!
# Propagating the integral control estimate to every elementary rank

The analytic residue in the integral route is rank three.  Once the finite
integral control set controls the six rank-three roots, identity padding
transports that estimate to every ordered root in `EL_n`.  Decomposing a
rectangular block root entry by entry then controls the block-root Kazhdan
subset.  This is the coefficient-free analogue of the finite-field padding
argument.

Consequently, one family of rank-three `ColumnPlaneMassBound` estimates over
finite-rank free `ℤ`-algebras implies the full elementary property-`(T)`
theorem over every finitely generated unital ring.  The implication is proved
here; the column-plane estimate itself is not assumed silently or asserted as
a theorem.
-/

namespace GroupApproximation
namespace EJZIntegralGeneralRankReduction

open IntegralCharacterMass
open FiniteFieldElementaryPropertyT
open SteinbergHigherRankFiniteControl

noncomputable section

variable (X : Type) [Fintype X]

/-- One padded integral control element: the unit coefficient or one free
generator, placed in an arbitrary ordered root of rank `n`. -/
def paddedIntegralControlElement (n : ℕ)
    (p : IndexedRoot (Fin n) × Option X) :
    elementaryGroup (Fin n) (FreeAlgebra ℤ X) :=
  elementaryRoot p.1.1.1 p.1.1.2 p.1.2
    (integralControlCoefficient X p.2)

/-- The finite integral control set in every ordered root of rank `n`. -/
def paddedIntegralControlSet (n : ℕ) :
    Finset (elementaryGroup (Fin n) (FreeAlgebra ℤ X)) := by
  classical
  exact (Finset.univ : Finset (IndexedRoot (Fin n) × Option X)).image
    (paddedIntegralControlElement X n)

theorem paddedIntegralControlElement_mem (n : ℕ)
    (p : IndexedRoot (Fin n) × Option X) :
    paddedIntegralControlElement X n p ∈ paddedIntegralControlSet X n := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-- A rank-three integral control estimate transports to all ordinary roots
in every rank. -/
theorem paddedIntegralControlSet_controls_rootSet
    (n : ℕ) (hn : 3 ≤ n) (C : ℝ)
    (hcontrol : ControlsSubsetDisplacement.{0, 0}
      (elementaryGroup (Fin 3) (FreeAlgebra ℤ X))
      (integralControlSet X)
      (elementaryA2System (FreeAlgebra ℤ X)).rootSet C) :
    ControlsSubsetDisplacement.{0, 0}
      (elementaryGroup (Fin n) (FreeAlgebra ℤ X))
      (paddedIntegralControlSet X n)
      (elementaryRootSet (Fin n) (FreeAlgebra ℤ X)) C := by
  classical
  intro E _ _ _ rho z hz delta hdelta hnear g hg
  obtain ⟨u, v, huv, a, rfl⟩ := hg
  obtain ⟨w, hwu, hwv⟩ := Fin.exists_ne_and_ne_of_two_lt u v (by omega)
  let e : Fin 3 ↪ Fin n := tripleEmbedding u w v hwu.symm huv hwv
  let rho3 : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →*
      (E ≃ₗᵢ[ℝ] E) :=
    rho.comp (ElementaryPadding.elementaryPad e)
  have hnear3 : ∀ s ∈ integralControlSet X,
      ‖rho3 s z - z‖ < delta := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    have hmap : ElementaryPadding.elementaryPad e
        (integralControlElement X p) =
        paddedIntegralControlElement X n
          (⟨(e p.1.1.1, e p.1.1.2), e.injective.ne p.1.2⟩, p.2) := by
      simp [integralControlElement, paddedIntegralControlElement]
    show ‖rho (ElementaryPadding.elementaryPad e
      (integralControlElement X p)) z - z‖ < delta
    rw [hmap]
    exact hnear _ (paddedIntegralControlElement_mem X n _)
  have hg3 : elementaryRoot (0 : Fin 3) 2 (by decide) a ∈
      (elementaryA2System (FreeAlgebra ℤ X)).rootSet :=
    ⟨0, 2, by decide, a, rfl⟩
  have hmove := hcontrol E rho3 z hz delta hdelta hnear3 _ hg3
  simpa [rho3, e] using hmove

/-- The transported ordinary-root estimate controls every rectangular block
root, with the finite entry-count loss `n²`. -/
theorem paddedIntegralControlSet_controls_blockRootSet
    (n : ℕ) (hn : 3 ≤ n) (C : ℝ) (hC : 0 < C)
    (hcontrol : ControlsSubsetDisplacement.{0, 0}
      (elementaryGroup (Fin 3) (FreeAlgebra ℤ X))
      (integralControlSet X)
      (elementaryA2System (FreeAlgebra ℤ X)).rootSet C) :
    ControlsSubsetDisplacement.{0, 0}
      (elementaryGroup (Fin n) (FreeAlgebra ℤ X))
      (paddedIntegralControlSet X n)
      (BlockElementary.blockElementaryA2System
        (FreeAlgebra ℤ X) n hn).rootSet
      ((n * n : ℕ) * C + 1) := by
  intro E _ _ _ rho z hz delta hdelta hnear g hg
  obtain ⟨i, j, hij, hgm⟩ := hg
  have hord := paddedIntegralControlSet_controls_rootSet
    X n hn C hcontrol E rho z hz delta hdelta hnear
  have hD : (0 : ℝ) ≤ C * delta := (mul_pos hC hdelta).le
  have hroot : ∀ (u v : Fin n) (huv : u ≠ v)
      (c : FreeAlgebra ℤ X),
      ‖rho (elementaryRoot u v huv c) z - z‖ ≤ C * delta := by
    intro u v huv c
    exact (hord _ ⟨u, v, huv, c, rfl⟩).le
  have hbound := BlockElementary.norm_blockRoot_displacement_le
    (blk := BlockElementary.finBlock n) hij rho z _ hD hroot g hgm
  rw [Fintype.card_fin] at hbound
  nlinarith

/-- A rank-three control estimate over the integral free algebra yields
property `(T)` in every rank.  The root-subset half is supplied
unconditionally by `A2MagicExponentFree`. -/
theorem freeIntegralGeneralRank_hasKazhdanPropertyT_of_rankThreeControl
    (C : ℝ) (hC : 0 < C)
    (hcontrol : ControlsSubsetDisplacement.{0, 0}
      (elementaryGroup (Fin 3) (FreeAlgebra ℤ X))
      (integralControlSet X)
      (elementaryA2System (FreeAlgebra ℤ X)).rootSet C)
    (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0}
      (elementaryGroup (Fin n) (FreeAlgebra ℤ X)) := by
  obtain ⟨kappa, hkappa⟩ :=
    A2MagicExponentFree.blockElementary_exists_rootSet_isKazhdan
      (FreeAlgebra ℤ X) n hn
  have hblockC : (0 : ℝ) < (n * n : ℕ) * C + 1 := by positivity
  exact ⟨paddedIntegralControlSet X n,
    kappa / (2 * ((n * n : ℕ) * C + 1)),
    IsKazhdanSubset.to_pair_of_controls hkappa hblockC
      (paddedIntegralControlSet_controls_blockRootSet
        X n hn C hC hcontrol)⟩

end

end EJZIntegralGeneralRankReduction

/-- The one remaining analytic family in the integral reduction: a uniform
column-plane estimate for each finite-rank free `ℤ`-algebra. -/
def IntegralFreeColumnPlaneMassBounds : Prop :=
  ∀ (X : Type) [Fintype X], ∃ C : ℝ, 0 ≤ C ∧
    IntegralCharacterMass.ColumnPlaneMassBound.{0, 0}
      (FreeAlgebra ℤ X) (IntegralCharacterMass.integralControlSet X) C

/-- The integral column-plane estimate implies property `(T)` in every rank
over every finite-rank free `ℤ`-algebra. -/
theorem integralFreeColumnPlaneMassBounds_implies_freeIntegralGeneralRank
    (hplane : IntegralFreeColumnPlaneMassBounds) :
    FreeIntegralGeneralRankElementaryPropertyT := by
  intro X _ n hn
  obtain ⟨C, hC, hplaneC⟩ := hplane X
  have hcontrol :=
    IntegralCharacterMass.integral_controlsRootSet_of_columnPlaneMassBound
      X hplaneC
  exact EJZIntegralGeneralRankReduction.freeIntegralGeneralRank_hasKazhdanPropertyT_of_rankThreeControl
      X (2 * C + 1) (by linarith) hcontrol n hn

/-- **Exact full reduction.**  The integral column-plane estimate implies the
Ershov--Jaikin-Zapirain property-`(T)` conclusion for every finitely generated
unital associative ring, in every characteristic and every rank `n ≥ 3`. -/
theorem integralFreeColumnPlaneMassBounds_implies_fullEJZ
    (hplane : IntegralFreeColumnPlaneMassBounds) :
    FinitelyGeneratedRingGeneralRankElementaryPropertyT :=
  freeIntegralGeneralRank_implies_finitelyGeneratedRingGeneralRank
    (integralFreeColumnPlaneMassBounds_implies_freeIntegralGeneralRank hplane)

/-- Closed form of the exact analytic reduction. -/
def PrintedEJZColumnPlaneReduction : Prop :=
  IntegralFreeColumnPlaneMassBounds →
    FinitelyGeneratedRingGeneralRankElementaryPropertyT

theorem printedEJZColumnPlaneReduction : PrintedEJZColumnPlaneReduction :=
  integralFreeColumnPlaneMassBounds_implies_fullEJZ

#audit_closed_axioms printedEJZColumnPlaneReduction

end GroupApproximation
