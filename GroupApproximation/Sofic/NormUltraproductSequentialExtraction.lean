import GroupApproximation.Sofic.OpAlmostRepresentation
import GroupApproximation.Sofic.NormMFResidualDetector

/-!
# Extracting a sequential model from an arbitrary norm ultraproduct

The definition of `NormMFInvisible` quantifies over an arbitrary index type
and ultrafilter, whereas the finite-stage Kazhdan machinery is sequential.
This file bridges that mismatch.  If a marked element survives in an
arbitrary operator-norm matrix ultraproduct, countability lets us choose one
index at each finite stage so that multiplication defects tend to zero and
the marked element stays a fixed positive distance from the identity.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-- An operator-norm almost representation in which one marked element stays
uniformly separated from the identity. -/
structure MarkedOpAlmostRepresentation (G : Type u) [Group G] (z : G)
    extends OpAlmostRepresentation G where
  separation : ℝ
  separation_pos : 0 < separation
  marked_separated : ∀ n,
    separation ≤ ‖(map n z : Matrix (model n) (model n) ℂ) - map n 1‖

/-- A lift of a homomorphism into a norm ultraproduct is multiplicative on an
ultrafilter-large set, at every prescribed positive tolerance. -/
theorem normUltraproduct_lift_eventually_multiplicative
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X)
    (lift : G → ∀ i, Matrix.unitaryGroup (X i) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g) :
    ∀ g h ε, 0 < ε → ∀ᶠ i in (U : Filter I),
      ‖(lift (g * h) i : Matrix (X i) (X i) ℂ) -
        (lift g i : Matrix (X i) (X i) ℂ) * lift h i‖ ≤ ε := by
  intro g h ε hε
  have heq : (QuotientGroup.mk (lift g * lift h) : UniversalWeakMF U X) =
      QuotientGroup.mk (lift (g * h)) := by
    rw [QuotientGroup.mk_mul, hlift, hlift, hlift, map_mul]
  have hnull : (lift g * lift h)⁻¹ * lift (g * h) ∈ nullOpSubgroup U X :=
    QuotientGroup.eq.mp heq
  filter_upwards [hnull ε hε] with i hi
  change opLength (X i) ((lift g i * lift h i)⁻¹ * lift (g * h) i) < ε at hi
  rw [opLength_inv_mul] at hi
  exact le_of_lt hi

/-- If the marked image is nontrivial, some fixed positive operator-norm gap
from the identity holds on an ultrafilter-large set of coordinates. -/
theorem normUltraproduct_lift_eventually_marked_separated
    {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X)
    (lift : G → ∀ i, Matrix.unitaryGroup (X i) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g)
    {z : G} (hz : rho z ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ i in (U : Filter I),
      δ ≤ ‖(lift z i : Matrix (X i) (X i) ℂ) - lift 1 i‖ := by
  have hz1 : rho z ≠ rho 1 := by simpa using hz
  have hnot : (lift 1)⁻¹ * lift z ∉ nullOpSubgroup U X := by
    intro hc
    apply hz1
    rw [← hlift z, ← hlift 1]
    exact (QuotientGroup.eq.mpr hc).symm
  have hex : ∃ δ : ℝ, 0 < δ ∧ ¬ (∀ᶠ i in (U : Filter I),
      opLength (X i) (((lift 1)⁻¹ * lift z) i) < δ) := by
    by_contra hcon
    apply hnot
    intro δ hδ
    by_contra hbad
    exact hcon ⟨δ, hδ, hbad⟩
  obtain ⟨δ, hδ, hnotEventually⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  have hcompl := (Ultrafilter.eventually_not (p := fun i ↦
    opLength (X i) (((lift 1)⁻¹ * lift z) i) < δ)).mpr hnotEventually
  filter_upwards [hcompl] with i hi
  change ¬ opLength (X i) ((lift 1 i)⁻¹ * lift z i) < δ at hi
  rw [opLength_inv_mul] at hi
  exact not_lt.mp hi

/-- **Arbitrary-ultrafilter to sequential extraction.**  A surviving marked
element in any norm-matrix ultraproduct yields a sequential operator-norm
almost representation retaining a uniform marked gap. -/
theorem exists_markedOpAlmostRepresentation_of_ne_one
    [Countable G] {I : Type} (U : Ultrafilter I) (X : I → FiniteModel)
    (rho : G →* UniversalWeakMF U X) {z : G} (hz : rho z ≠ 1) :
    Nonempty (MarkedOpAlmostRepresentation G z) := by
  classical
  choose lift hlift using fun g : G ↦ QuotientGroup.mk_surjective (rho g)
  have hmul := normUltraproduct_lift_eventually_multiplicative U X rho lift hlift
  obtain ⟨δ, hδ, hsep⟩ :=
    normUltraproduct_lift_eventually_marked_separated U X rho lift hlift hz
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨k, rfl⟩ := he g
    exact ⟨k, fun n hn ↦ hFmono hn (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨k, Finset.self_mem_range_succ k, rfl⟩))⟩
  let η : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hall : ∀ n : ℕ, ∀ᶠ i in (U : Filter I),
      (∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) i : Matrix (X i) (X i) ℂ) -
          (lift p.1 i : Matrix (X i) (X i) ℂ) * lift p.2 i‖ ≤ η n) ∧
      δ ≤ ‖(lift z i : Matrix (X i) (X i) ℂ) - lift 1 i‖ := by
    intro n
    have hm : ∀ᶠ i in (U : Filter I), ∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) i : Matrix (X i) (X i) ℂ) -
          (lift p.1 i : Matrix (X i) (X i) ℂ) * lift p.2 i‖ ≤ η n := by
      rw [eventually_all_finset]
      intro p _
      exact hmul p.1 p.2 (η n) (hη n)
    exact hm.and hsep
  let stage : ℕ → I := fun n ↦ Classical.choose (hall n).exists
  have hstage (n : ℕ) :
      (∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) -
          (lift p.1 (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) *
            lift p.2 (stage n)‖ ≤ η n) ∧
      δ ≤ ‖(lift z (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) -
        lift 1 (stage n)‖ := Classical.choose_spec (hall n).exists
  have hmodelPos (n : ℕ) : 0 < Fintype.card (X (stage n)) := by
    rw [Fintype.card_pos_iff]
    by_contra hempty
    haveI : IsEmpty (X (stage n)) := not_nonempty_iff.mp hempty
    have heq : (lift z (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) =
        lift 1 (stage n) := by
      ext i
      exact isEmptyElim i
    have := (hstage n).2
    rw [heq, sub_self, norm_zero] at this
    exact (not_lt_of_ge this) hδ
  refine ⟨{
    separation := δ
    separation_pos := hδ
    model := fun n ↦ X (stage n)
    modelNonempty := hmodelPos
    map := fun n g ↦ lift g (stage n)
    asymptoticallyMultiplicative := ?_
    marked_separated := fun n ↦ (hstage n).2 }⟩
  intro g h ε hε
  obtain ⟨Ng, hNg⟩ := hFmem g
  obtain ⟨Nh, hNh⟩ := hFmem h
  obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
  refine ⟨max (max Ng Nh) Ne, fun n hn ↦ ?_⟩
  have hg : g ∈ F n := hNg n ((le_max_left _ _).trans
    ((le_max_left _ _).trans hn))
  have hh : h ∈ F n := hNh n ((le_max_right _ _).trans
    ((le_max_left _ _).trans hn))
  have hsmall : η n ≤ ε := by
    dsimp [η]
    have hNen : (Ne : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_max_right (max Ng Nh) Ne).trans hn
    have hlt : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hlt
    linarith
  exact ((hstage n).1 (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)).trans hsmall

/-- To prove that a marked element is invisible in every arbitrary norm
ultraproduct, it suffices to rule out sequential operator-norm almost
representations retaining a uniform marked gap.  This is the exact logical
interface consumed by the sequential Kazhdan-compression argument. -/
theorem normMFInvisible_of_no_markedOpAlmostRepresentation
    [Countable G] {z : G}
    (hkill : MarkedOpAlmostRepresentation G z → False) :
    NormMFInvisible z := by
  intro I U X rho
  by_contra hz
  obtain ⟨A⟩ := exists_markedOpAlmostRepresentation_of_ne_one U X rho hz
  exact hkill A

end GroupApproximation
