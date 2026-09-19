import GroupApproximation.Sofic.HyperlinearUltraproduct
import GroupApproximation.Sofic.HyperlinearWeakBridge
import Mathlib.Order.Filter.Finite

/-!
# The tracial-ultraproduct characterization, elementary direction

An injective homomorphism into a metric ultraproduct of finite unitary groups
produces hyperlinear models.  Representatives of finitely many group elements
are simultaneously approximately multiplicative on an ultrafilter-large set.
Injectivity says that each of the finitely many distinct pairs has some
positive Hilbert--Schmidt separation on an ultrafilter-large set; taking the
minimum gives a common positive separation.  Equal-size identity padding and
conjugate-double amplification then turn that finite-set-dependent separation
into the convention used by `IsHyperlinear`.
-/

namespace GroupApproximation

open Filter Matrix

variable {G : Type*} [Group G]
variable {iota : Type*} (U : Ultrafilter iota) (X : iota → FiniteModel)
variable (hX : ∀ i, 0 < Fintype.card (X i))

/-- **An embedding into a tracial matrix ultraproduct makes the source
hyperlinear.**  No countability assumption is needed because the construction
chooses representatives only on the finite test set currently under study. -/
theorem isHyperlinear_of_hyperlinearUltraproductEmbedding
    (f : G →* UniversalHyperlinear U X hX) (hf : Function.Injective f) :
    IsHyperlinear G := by
  classical
  let r : G → ∀ i, Matrix.unitaryGroup (X i) ℂ := fun g ↦ Quotient.out (f g)
  have hr (g : G) : QuotientGroup.mk (r g) = f g :=
    Quotient.out_eq' (f g)
  have hlen (i : iota) (a b : Matrix.unitaryGroup (X i) ℂ) :
      hsLengthSq (X i) ((a⁻¹ * b : Matrix.unitaryGroup (X i) ℂ)) =
        hsDistSq (X i) b a := by
    rw [coe_inv_mul]
    exact hsLengthSq_conjTranspose_mul (X i) a.2 (hX i)
  have hmul (g k : G) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ i in (U : Filter iota),
        hsDistSq (X i) (r (g * k) i)
          ((r g i : Matrix (X i) (X i) ℂ) * r k i) < ε := by
    have heq : (QuotientGroup.mk (r g * r k) :
        UniversalHyperlinear U X hX) = QuotientGroup.mk (r (g * k)) := by
      calc
        (QuotientGroup.mk (r g * r k) : UniversalHyperlinear U X hX) =
            QuotientGroup.mk (r g) * QuotientGroup.mk (r k) := by
              rw [QuotientGroup.mk_mul]
        _ = f g * f k := by rw [hr, hr]
        _ = f (g * k) := (map_mul f g k).symm
        _ = QuotientGroup.mk (r (g * k)) := (hr (g * k)).symm
    have hnull : (r g * r k)⁻¹ * r (g * k) ∈
        nullUnitarySubgroup U X hX := QuotientGroup.eq.mp heq
    filter_upwards [hnull ε hε] with i hi
    rw [show hsLengthSq (X i) (((r g * r k)⁻¹ * r (g * k)) i) =
        hsDistSq (X i) (r (g * k) i) ((r g * r k) i) by
          exact hlen i ((r g * r k) i) (r (g * k) i)] at hi
    exact hi
  have hsepPair (g k : G) (hgk : g ≠ k) :
      ∃ delta : ℝ, 0 < delta ∧
        ∀ᶠ i in (U : Filter iota),
          delta ≤ hsDistSq (X i) (r g i) (r k i) := by
    have hclasses : (QuotientGroup.mk (r g) :
        UniversalHyperlinear U X hX) ≠ QuotientGroup.mk (r k) := by
      rw [hr, hr]
      exact fun h ↦ hgk (hf h)
    have hnnull : ¬ IsNullUnitarySeq U X ((r k)⁻¹ * r g) := by
      intro hnull
      apply hclasses
      exact (QuotientGroup.eq.mpr hnull).symm
    rw [IsNullUnitarySeq] at hnnull
    push Not at hnnull
    obtain ⟨delta, hdelta, hnot⟩ := hnnull
    refine ⟨delta, hdelta, ?_⟩
    filter_upwards [hnot] with i hi
    rw [show hsLengthSq (X i) (((r k)⁻¹ * r g) i) =
        hsDistSq (X i) (r g i) (r k i) by
          exact hlen i (r k i) (r g i)] at hi
    exact hi
  have hfiniteSep (P : Finset (G × G))
      (hP : ∀ p ∈ P, p.1 ≠ p.2) :
      ∃ delta : ℝ, 0 < delta ∧
        ∀ p ∈ P, ∀ᶠ i in (U : Filter iota),
          delta ≤ hsDistSq (X i) (r p.1 i) (r p.2 i) := by
    induction P using Finset.induction_on with
    | empty =>
        exact ⟨1, by norm_num, by simp⟩
    | @insert p P hp ih =>
        obtain ⟨dp, hdp, hevp⟩ := hsepPair p.1 p.2
          (hP p (Finset.mem_insert_self p P))
        obtain ⟨dP, hdP, hevP⟩ := ih fun q hq ↦
          hP q (Finset.mem_insert_of_mem hq)
        refine ⟨min dp dP, lt_min hdp hdP, ?_⟩
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hevp.mono fun i hi ↦ (min_le_left _ _).trans hi
        · exact (hevP q hq).mono fun i hi ↦ (min_le_right _ _).trans hi
  apply isHyperlinear_of_isHyperlinearNonScalar
  intro F
  let P : Finset (G × G) := (F ×ˢ F).filter fun p ↦ p.1 ≠ p.2
  have hP : ∀ p ∈ P, p.1 ≠ p.2 := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨delta, hdelta, hsep⟩ := hfiniteSep P hP
  refine ⟨delta / 4, by positivity, ?_⟩
  intro ε hε
  have hmulAll : ∀ᶠ i in (U : Filter iota),
      ∀ p ∈ F ×ˢ F, hsDistSq (X i) (r (p.1 * p.2) i)
        ((r p.1 i : Matrix (X i) (X i) ℂ) * r p.2 i) < ε := by
    rw [Finset.eventually_all]
    intro p hp
    exact hmul p.1 p.2 ε hε
  have hsepAll : ∀ᶠ i in (U : Filter iota),
      ∀ p ∈ P, delta ≤ hsDistSq (X i) (r p.1 i) (r p.2 i) := by
    rw [Finset.eventually_all]
    exact hsep
  obtain ⟨i, hiMul, hiSep⟩ := (hmulAll.and hsepAll).exists
  let M : WeakHyperlinearModel G F delta ε := {
    carrier := X i
    nonempty := hX i
    map := fun g ↦ r g i
    isUnitary := fun g ↦ (r g i).2
    multiplicative := by
      intro g hg k hk
      exact (hiMul (g, k) (Finset.mem_product.mpr ⟨hg, hk⟩)).le
    separated := by
      intro g hg k hk hgk
      exact hiSep (g, k) (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hg, hk⟩, hgk⟩) }
  exact ⟨M.padToNonScalar⟩

end GroupApproximation
