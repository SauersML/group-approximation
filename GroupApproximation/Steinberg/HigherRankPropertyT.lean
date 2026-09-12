import GroupApproximation.Steinberg.BlockKazhdan
import GroupApproximation.Steinberg.HigherRankFiniteControl
import Mathlib.RingTheory.FiniteType

/-!
# Property `(T)` in higher Steinberg rank over self-similar finite-type rings

The three-block system supplies the infinite Kazhdan subset.  The finite
control set is descended from a finite free algebra and transported across a
finite index equivalence.
-/

namespace GroupApproximation

open SteinbergGroup
open SteinbergHigherRankFiniteControl
open SteinbergRootPlaneFourier

noncomputable section

variable {R I κ X : Type*} [Ring R] [Fintype I] [DecidableEq I]
  [Fintype κ] [DecidableEq κ] [Fintype X]

/-- A canonical enumeration of an arbitrary finite index type. -/
def finIndexEquiv (I : Type*) [Fintype I] : Fin (Fintype.card I) ≃ I :=
  (Fintype.equivFin I).symm

/-- Map the standard free-algebra controls first across an index equivalence
and then through a coefficient-ring quotient. -/
def quotientControlSet
    (f : SteinbergRootPlaneFourier.FreeRing X →+* R) :
    Finset (SteinbergGroup I R) := by
  classical
  exact (finiteControlSetAt X (Fintype.card I)).image fun s ↦
    SteinbergGroup.ringMap (I := I) f
      (SteinbergGroup.reindexEquiv (finIndexEquiv I) s)

/-- The descended finite controls uniformly control every ordinary root in
the target Steinberg group. -/
theorem quotientControlSet_controls_rootSet
    (f : SteinbergRootPlaneFourier.FreeRing X →+* R)
    (hf : Function.Surjective f) (hcard : 3 ≤ Fintype.card I) :
    ControlsSubsetDisplacement (SteinbergGroup I R) (quotientControlSet f)
      (SteinbergGroup.rootSet (I := I) (R := R))
      (12 * Fintype.card X + 13 : ℝ) := by
  classical
  intro E _ _ _ rho z hz δ hδ hnear g hg
  rcases hg with ⟨i, j, hij, a, rfl⟩
  obtain ⟨a₀, ha₀⟩ := hf a
  let e := finIndexEquiv I
  let phi : SteinbergGroup (Fin (Fintype.card I))
      (SteinbergRootPlaneFourier.FreeRing X) →*
      SteinbergGroup I R :=
    (SteinbergGroup.ringMap (I := I) f).comp
      (SteinbergGroup.reindexEquiv e).toMonoidHom
  let rho₀ := rho.comp phi
  have hnear₀ : ∀ s ∈ finiteControlSetAt X (Fintype.card I),
      ‖rho₀ s z - z‖ < δ := by
    intro s hs
    exact hnear _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hroot : x (e.symm i) (e.symm j) (e.symm.injective.ne hij) a₀ ∈
      SteinbergGroup.rootSet (I := Fin (Fintype.card I))
        (R := SteinbergRootPlaneFourier.FreeRing X) :=
    ⟨e.symm i, e.symm j, e.symm.injective.ne hij, ⟨a₀, rfl⟩⟩
  have hmove := finiteControlSetAt_controls_rootSet X
    (Fintype.card I) hcard E rho₀ z hz δ hδ hnear₀ _ hroot
  have hphi : phi
      (x (e.symm i) (e.symm j) (e.symm.injective.ne hij) a₀) =
      x i j hij a := by
    change SteinbergGroup.ringMap (I := I) f
      (SteinbergGroup.indexMap e.toEmbedding
        (x (e.symm i) (e.symm j) (e.symm.injective.ne hij) a₀)) = _
    rw [SteinbergGroup.indexMap_x, SteinbergGroup.ringMap_x, ha₀]
    simp
  change ‖rho (phi
    (x (e.symm i) (e.symm j) (e.symm.injective.ne hij) a₀)) z - z‖ < _ at hmove
  rw [hphi] at hmove
  exact hmove

/-- Displacement by a finite commuting product is bounded by the sum of the
displacements of its factors. -/
theorem norm_noncommProd_displacement_le
    {G E α : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (z : E) (s : Finset α) (u : α → G)
    (hu : (s : Set α).Pairwise (Function.onFun Commute u)) :
    ‖rho (s.noncommProd u hu) z - z‖ ≤
      ∑ i ∈ s, ‖rho (u i) z - z‖ := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons i s hi ih =>
      rw [Finset.noncommProd_cons, Finset.sum_cons hi]
      exact (A2System.norm_mul_displacement_le rho z _ _).trans
        (add_le_add le_rfl (ih (hu.mono fun _ ↦ Finset.mem_cons.2 ∘ .inr)))

/-- The descended free controls also control the six rectangular block
roots, with only the finite tail-cardinality loss. -/
theorem quotientControlSet_controls_blockRootSet
    (F : CompleteMatrixFamily R κ)
    (f : SteinbergRootPlaneFourier.FreeRing X →+* R)
    (hf : Function.Surjective f)
    (hcard : 3 ≤ Fintype.card (Fin 2 ⊕ κ)) :
    ControlsSubsetDisplacement (SteinbergGroup (Fin 2 ⊕ κ) R)
      (quotientControlSet f) (SteinbergBlockRoot.blockA2System F).rootSet
      ((Fintype.card κ + 1 : ℝ) *
        (12 * Fintype.card X + 13 : ℝ)) := by
  classical
  let C : ℝ := 12 * Fintype.card X + 13
  have hC : 0 < C := by dsimp [C]; positivity
  have hordinary := quotientControlSet_controls_rootSet f hf hcard
  intro E _ _ _ rho z hz δ hδ hnear g hg
  rcases hg with ⟨i, j, hij, hg⟩
  by_cases hi : i = 2
  · subst i
    have hj : j ≠ 2 := by omega
    simp [SteinbergBlockRoot.blockA2System,
      SteinbergBlockRoot.blockRootSubgroup,
      SteinbergBlockRoot.singletonOfNotTail] at hg
    obtain ⟨a, rfl⟩ := hg
    change ‖rho (SteinbergBlockRoot.tailToRow F
      (SteinbergBlockRoot.singletonOfNotTail j hj) a) z - z‖ < _
    unfold SteinbergBlockRoot.tailToRow
    have hprod := norm_noncommProd_displacement_le rho z Finset.univ
      (fun k ↦ x (Sum.inr k) (Sum.inl
        (SteinbergBlockRoot.singletonOfNotTail j hj)) (by simp)
        (F.right k * a))
      (SteinbergBlockRoot.tailToRow_pairwise F
        (SteinbergBlockRoot.singletonOfNotTail j hj) a)
    have hsum : (∑ k : κ, ‖rho
        (x (Sum.inr k) (Sum.inl
          (SteinbergBlockRoot.singletonOfNotTail j hj)) (by simp)
          (F.right k * a)) z - z‖) ≤ Fintype.card κ * (C * δ) := by
      calc
        _ ≤ ∑ _k : κ, C * δ := by
          apply Finset.sum_le_sum
          intro k _
          exact (hordinary E rho z hz δ hδ hnear _
            ⟨Sum.inr k, Sum.inl
              (SteinbergBlockRoot.singletonOfNotTail j hj), by simp,
              ⟨F.right k * a, rfl⟩⟩).le
        _ = Fintype.card κ * (C * δ) := by simp
    calc
      _ ≤ ∑ k : κ, ‖rho
          (x (Sum.inr k) (Sum.inl
            (SteinbergBlockRoot.singletonOfNotTail j hj)) (by simp)
            (F.right k * a)) z - z‖ := by simpa using hprod
      _ ≤ Fintype.card κ * (C * δ) := hsum
      _ < ((Fintype.card κ + 1 : ℝ) *
          (12 * Fintype.card X + 13 : ℝ)) * δ := by
        dsimp [C] at hC ⊢
        nlinarith
  · by_cases hj : j = 2
    · subst j
      simp [SteinbergBlockRoot.blockA2System,
        SteinbergBlockRoot.blockRootSubgroup,
        SteinbergBlockRoot.singletonOfNotTail, hi] at hg
      obtain ⟨a, rfl⟩ := hg
      change ‖rho (SteinbergBlockRoot.rowToTail F
        (SteinbergBlockRoot.singletonOfNotTail i hi) a) z - z‖ < _
      unfold SteinbergBlockRoot.rowToTail
      have hprod := norm_noncommProd_displacement_le rho z Finset.univ
        (fun k ↦ x (Sum.inl
          (SteinbergBlockRoot.singletonOfNotTail i hi)) (Sum.inr k)
          (by simp) (a * F.left k))
        (SteinbergBlockRoot.rowToTail_pairwise F
          (SteinbergBlockRoot.singletonOfNotTail i hi) a)
      have hsum : (∑ k : κ, ‖rho
          (x (Sum.inl (SteinbergBlockRoot.singletonOfNotTail i hi))
            (Sum.inr k) (by simp) (a * F.left k)) z - z‖) ≤
          Fintype.card κ * (C * δ) := by
        calc
          _ ≤ ∑ _k : κ, C * δ := by
            apply Finset.sum_le_sum
            intro k _
            exact (hordinary E rho z hz δ hδ hnear _
              ⟨Sum.inl (SteinbergBlockRoot.singletonOfNotTail i hi),
                Sum.inr k, by simp, ⟨a * F.left k, rfl⟩⟩).le
          _ = Fintype.card κ * (C * δ) := by simp
      calc
        _ ≤ ∑ k : κ, ‖rho
            (x (Sum.inl (SteinbergBlockRoot.singletonOfNotTail i hi))
              (Sum.inr k) (by simp) (a * F.left k)) z - z‖ := by
          simpa using hprod
        _ ≤ Fintype.card κ * (C * δ) := hsum
        _ < ((Fintype.card κ + 1 : ℝ) *
            (12 * Fintype.card X + 13 : ℝ)) * δ := by
          dsimp [C] at hC ⊢
          nlinarith
    · simp [SteinbergBlockRoot.blockA2System,
        SteinbergBlockRoot.blockRootSubgroup,
        SteinbergBlockRoot.singletonOfNotTail,
        SteinbergBlockRoot.smallRootSubgroup, hi, hj] at hg
      obtain ⟨a, rfl⟩ := hg
      change ‖rho (x
        (Sum.inl (SteinbergBlockRoot.singletonOfNotTail i hi))
        (Sum.inl (SteinbergBlockRoot.singletonOfNotTail j hj))
        (by simpa using SteinbergBlockRoot.singletonOfNotTail_ne i j hi hj hij)
        a) z - z‖ < _
      have hmove := hordinary E rho z hz δ hδ hnear _
        ⟨Sum.inl (SteinbergBlockRoot.singletonOfNotTail i hi),
          Sum.inl (SteinbergBlockRoot.singletonOfNotTail j hj),
          (by simpa using SteinbergBlockRoot.singletonOfNotTail_ne i j hi hj hij),
          ⟨a, rfl⟩⟩
      have hfactor : C * δ ≤ (Fintype.card κ + 1 : ℝ) * C * δ := by
        calc
          C * δ ≤ (Fintype.card κ + 1 : ℝ) * (C * δ) :=
            le_mul_of_one_le_left (mul_nonneg hC.le hδ.le) (by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Fintype.card κ)))
          _ = (Fintype.card κ + 1 : ℝ) * C * δ := by ring
      exact hmove.trans_le hfactor

/-- A finite-type characteristic-two coefficient ring with a nonempty
complete matrix family has property `(T)` in the corresponding `2 + |κ|`
Steinberg rank. -/
theorem finiteTypeBlockSteinberg_hasKazhdanPropertyT
    [Algebra (ZMod 2) R] [Algebra.FiniteType (ZMod 2) R] [CharP R 2]
    (F : CompleteMatrixFamily R κ) (hκ : 0 < Fintype.card κ) :
    HasKazhdanPropertyT (SteinbergGroup (Fin 2 ⊕ κ) R) := by
  obtain ⟨Y, hY, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := ZMod 2) (A := R)).mp inferInstance
  letI : Fintype Y := hY
  have hcard : 3 ≤ Fintype.card (Fin 2 ⊕ κ) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨kappa, hkappa⟩ :=
    SteinbergBlockRoot.blockA2_exists_rootSet_isKazhdan F 2 (by omega)
  let C : ℝ := (Fintype.card κ + 1 : ℝ) *
    (12 * Fintype.card Y + 13 : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hcontrol := quotientControlSet_controls_blockRootSet
    F f.toRingHom hf hcard
  let epsilon := kappa / (2 * C)
  have hpair : IsKazhdanPair (SteinbergGroup (Fin 2 ⊕ κ) R)
      (quotientControlSet f.toRingHom) epsilon := by
    exact IsKazhdanSubset.to_pair_of_controls hkappa hC hcontrol
  exact ⟨quotientControlSet f.toRingHom, epsilon, hpair⟩

end
end GroupApproximation
