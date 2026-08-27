import GroupApproximation.Sofic.SoficAction
import Mathlib.Algebra.Group.Action.Sum
import Mathlib.Data.Fintype.Sum

/-!
# Sofic actions on disjoint unions

**Lemma 30.4** of the dossier, in its essential two-piece form: sofic actions are
closed under disjoint unions.  A finite window meets only finitely many pieces,
so gluing finitely many orbit models is this statement iterated.

The model is the product of the two models: the site sets multiply, the
approximating maps act coordinatewise, the good sets multiply, and the chart
target is the disjoint union of the two chart targets.  The multiplicativity
estimate is `permDist_prodCongr_le`, which says that a product permutation is at
most as far from another product as the sum of the coordinate distances.
-/

namespace GroupApproximation

universe u v

/-! ## Product permutations -/

section Prod

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem prodCongr_mul (p p' : Equiv.Perm A) (q q' : Equiv.Perm B) :
    Equiv.prodCongr p q * Equiv.prodCongr p' q'
      = Equiv.prodCongr (p * p') (q * q') :=
  Equiv.ext fun _ => rfl

/-- A product permutation is at most as far from another product as the sum of
the coordinate distances. -/
theorem permDist_prodCongr_le (p₁ q₁ : Equiv.Perm A) (p₂ q₂ : Equiv.Perm B) :
    permDist (Equiv.prodCongr p₁ p₂) (Equiv.prodCongr q₁ q₂)
      ≤ permDist p₁ q₁ + permDist p₂ q₂ := by
  classical
  by_cases hA : Fintype.card A = 0
  · have : Fintype.card (A × B) = 0 := by rw [Fintype.card_prod, hA, zero_mul]
    simp only [permDist, this, Nat.cast_zero, div_zero]
    exact add_nonneg (permDist_nonneg _ _) (permDist_nonneg _ _)
  by_cases hB : Fintype.card B = 0
  · have : Fintype.card (A × B) = 0 := by rw [Fintype.card_prod, hB, mul_zero]
    simp only [permDist, this, Nat.cast_zero, div_zero]
    exact add_nonneg (permDist_nonneg _ _) (permDist_nonneg _ _)
  have hApos : (0 : ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hA
  have hBpos : (0 : ℝ) < (Fintype.card B : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hB
  set D : Finset (A × B) := Finset.univ.filter
    (fun z => Equiv.prodCongr p₁ p₂ z ≠ Equiv.prodCongr q₁ q₂ z) with hD
  set D₁ : Finset A := Finset.univ.filter (fun a => p₁ a ≠ q₁ a) with hD₁
  set D₂ : Finset B := Finset.univ.filter (fun b => p₂ b ≠ q₂ b) with hD₂
  have hsub : D ⊆ (D₁ ×ˢ (Finset.univ : Finset B)) ∪
      ((Finset.univ : Finset A) ×ˢ D₂) := by
    intro z hz
    rw [hD, Finset.mem_filter] at hz
    by_cases h1 : p₁ z.1 = q₁ z.1
    · have h2 : p₂ z.2 ≠ q₂ z.2 := by
        intro hcon
        exact hz.2 (Prod.ext h1 hcon)
      refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [hD₂]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
    · refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩)
      rw [hD₁]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
  have hcard : (D.card : ℝ)
      ≤ (D₁.card : ℝ) * (Fintype.card B : ℝ)
        + (Fintype.card A : ℝ) * (D₂.card : ℝ) := by
    have hnat : D.card ≤ D₁.card * Fintype.card B + Fintype.card A * D₂.card := by
      calc D.card ≤ ((D₁ ×ˢ (Finset.univ : Finset B)) ∪
              ((Finset.univ : Finset A) ×ˢ D₂)).card := Finset.card_le_card hsub
        _ ≤ (D₁ ×ˢ (Finset.univ : Finset B)).card
              + ((Finset.univ : Finset A) ×ˢ D₂).card := Finset.card_union_le _ _
        _ = D₁.card * Fintype.card B + Fintype.card A * D₂.card := by
            rw [Finset.card_product, Finset.card_product, Finset.card_univ,
              Finset.card_univ]
    exact_mod_cast hnat
  have hA' : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hApos
  have hB' : (Fintype.card B : ℝ) ≠ 0 := ne_of_gt hBpos
  have hexp : ((D₁.card : ℝ) / (Fintype.card A : ℝ)
        + (D₂.card : ℝ) / (Fintype.card B : ℝ)) *
      ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))
      = (D₁.card : ℝ) * (Fintype.card B : ℝ)
        + (Fintype.card A : ℝ) * (D₂.card : ℝ) := by
    field_simp
  have hprodpos : (0 : ℝ) < ((Fintype.card A * Fintype.card B : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_pos hApos hBpos
  rw [permDist, permDist, permDist, ← hD, ← hD₁, ← hD₂, Fintype.card_prod]
  rw [div_le_iff₀ hprodpos, Nat.cast_mul, hexp]
  exact hcard

end Prod

/-! ## The disjoint union of two sofic actions -/

section Sum

variable {G : Type u} [Group G] {X Y : Type v} [MulAction G X] [MulAction G Y]

/-- **Lemma 30.4, two-piece form.**  Sofic actions are closed under disjoint
unions.  A finite window meets only finitely many orbits, so gluing finitely many
orbit models is this statement iterated. -/
theorem isSoficAction_sum [DecidableEq X] [DecidableEq Y]
    (hX : IsSoficAction G X) (hY : IsSoficAction G Y) :
    IsSoficAction G (X ⊕ Y) := by
  classical
  intro F E ε hε
  have hhalf : (0 : ℝ) < ε / 2 := by positivity
  set E₁ : Finset X := E.biUnion
    (fun z => Sum.elim (fun x => ({x} : Finset X)) (fun _ => (∅ : Finset X)) z)
    with hE₁def
  set E₂ : Finset Y := E.biUnion
    (fun z => Sum.elim (fun _ => (∅ : Finset Y)) (fun y => ({y} : Finset Y)) z)
    with hE₂def
  have hE₁ : ∀ x : X, x ∈ E₁ ↔ (Sum.inl x : X ⊕ Y) ∈ E := by
    intro x
    rw [hE₁def, Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hx⟩
      cases z with
      | inl x' =>
          rw [Sum.elim_inl, Finset.mem_singleton] at hx
          exact hx ▸ hz
      | inr y => simp at hx
    · intro h
      exact ⟨Sum.inl x, h, by simp⟩
  have hE₂ : ∀ y : Y, y ∈ E₂ ↔ (Sum.inr y : X ⊕ Y) ∈ E := by
    intro y
    rw [hE₂def, Finset.mem_biUnion]
    constructor
    · rintro ⟨z, hz, hy⟩
      cases z with
      | inl x => simp at hy
      | inr y' =>
          rw [Sum.elim_inr, Finset.mem_singleton] at hy
          exact hy ▸ hz
    · intro h
      exact ⟨Sum.inr y, h, by simp⟩
  obtain ⟨M₁⟩ := hX F E₁ (ε / 2) hhalf
  obtain ⟨M₂⟩ := hY F E₂ (ε / 2) hhalf
  letI : Fintype M₁.Chart := M₁.chartFintype
  letI : Fintype M₂.Chart := M₂.chartFintype
  letI : Fintype M₁.Site := M₁.siteFintype
  letI : Fintype M₂.Site := M₂.siteFintype
  letI : DecidableEq M₁.Site := M₁.siteDecEq
  letI : DecidableEq M₂.Site := M₂.siteDecEq
  refine ⟨{
    Site := M₁.Site × M₂.Site
    siteFintype := inferInstance
    siteDecEq := inferInstance
    siteNonempty := by
      rw [Fintype.card_prod]
      exact Nat.mul_pos M₁.siteNonempty M₂.siteNonempty
    act := fun g => Equiv.prodCongr (M₁.act g) (M₂.act g)
    act_one := by rw [M₁.act_one, M₂.act_one]; exact Equiv.ext fun _ => rfl
    act_mul := ?_
    good := M₁.good ×ˢ M₂.good
    good_card := ?_
    Chart := M₁.Chart ⊕ M₂.Chart
    chartFintype := inferInstance
    chart := fun s z =>
      Sum.elim (fun x => Sum.inl (M₁.chart s.1 x))
        (fun y => Sum.inr (M₂.chart s.2 y)) z
    chart_inj := ?_
    chart_equivariant := ?_ }⟩
  · intro g hg h hh
    rw [prodCongr_mul]
    refine le_trans (permDist_prodCongr_le _ _ _ _) ?_
    have h1 := M₁.act_mul g hg h hh
    have h2 := M₂.act_mul g hg h hh
    linarith
  · rw [Finset.card_product, Fintype.card_prod]
    have h1 : (1 - ε / 2) * (Fintype.card M₁.Site : ℝ) ≤ (M₁.good.card : ℝ) :=
      M₁.good_card
    have h2 : (1 - ε / 2) * (Fintype.card M₂.Site : ℝ) ≤ (M₂.good.card : ℝ) :=
      M₂.good_card
    have hn1 : (0 : ℝ) ≤ (Fintype.card M₁.Site : ℝ) := Nat.cast_nonneg _
    have hn2 : (0 : ℝ) ≤ (Fintype.card M₂.Site : ℝ) := Nat.cast_nonneg _
    have hg1 : (0 : ℝ) ≤ (M₁.good.card : ℝ) := Nat.cast_nonneg _
    have hg2 : (0 : ℝ) ≤ (M₂.good.card : ℝ) := Nat.cast_nonneg _
    push_cast
    by_cases hε1 : ε ≤ 1
    · have hpos : (0 : ℝ) ≤ 1 - ε / 2 := by linarith
      have hprod : ((1 - ε / 2) * (Fintype.card M₁.Site : ℝ)) *
            ((1 - ε / 2) * (Fintype.card M₂.Site : ℝ))
          ≤ (M₁.good.card : ℝ) * (M₂.good.card : ℝ) :=
        mul_le_mul h1 h2 (by positivity) hg1
      have hLS : (0 : ℝ) ≤ (Fintype.card M₁.Site : ℝ) * (Fintype.card M₂.Site : ℝ) :=
        mul_nonneg hn1 hn2
      have hcoef : (1 - ε) ≤ (1 - ε / 2) * (1 - ε / 2) := by
        nlinarith [sq_nonneg ε]
      calc (1 - ε) * ((Fintype.card M₁.Site : ℝ) * (Fintype.card M₂.Site : ℝ))
          ≤ ((1 - ε / 2) * (1 - ε / 2)) *
              ((Fintype.card M₁.Site : ℝ) * (Fintype.card M₂.Site : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoef hLS
        _ = ((1 - ε / 2) * (Fintype.card M₁.Site : ℝ)) *
              ((1 - ε / 2) * (Fintype.card M₂.Site : ℝ)) := by ring
        _ ≤ (M₁.good.card : ℝ) * (M₂.good.card : ℝ) := hprod
    · have hε1' : 1 < ε := lt_of_not_ge hε1
      nlinarith [mul_nonneg hg1 hg2, mul_nonneg hn1 hn2]
  · intro s hs z hz w hw hzw
    rw [Finset.mem_product] at hs
    cases z with
    | inl x =>
        cases w with
        | inl x' =>
            rw [Sum.elim_inl, Sum.elim_inl] at hzw
            have := M₁.chart_inj s.1 hs.1 x ((hE₁ x).mpr hz) x' ((hE₁ x').mpr hw)
              (Sum.inl_injective hzw)
            exact congrArg Sum.inl this
        | inr y' => simp at hzw
    | inr y =>
        cases w with
        | inl x' => simp at hzw
        | inr y' =>
            rw [Sum.elim_inr, Sum.elim_inr] at hzw
            have := M₂.chart_inj s.2 hs.2 y ((hE₂ y).mpr hz) y' ((hE₂ y').mpr hw)
              (Sum.inr_injective hzw)
            exact congrArg Sum.inr this
  · intro g hg s hs hgs z hz hgz
    rw [Finset.mem_product] at hs hgs
    cases z with
    | inl x =>
        have hact : (g⁻¹ • (Sum.inl x : X ⊕ Y)) = Sum.inl (g⁻¹ • x) := rfl
        have hgx : g⁻¹ • x ∈ E₁ := by
          refine (hE₁ _).mpr ?_
          rw [← hact]
          exact hgz
        simp only [hact, Sum.elim_inl]
        exact congrArg Sum.inl
          (M₁.chart_equivariant g hg s.1 hs.1 hgs.1 x ((hE₁ x).mpr hz) hgx)
    | inr y =>
        have hact : (g⁻¹ • (Sum.inr y : X ⊕ Y)) = Sum.inr (g⁻¹ • y) := rfl
        have hgy : g⁻¹ • y ∈ E₂ := by
          refine (hE₂ _).mpr ?_
          rw [← hact]
          exact hgz
        simp only [hact, Sum.elim_inr]
        exact congrArg Sum.inr
          (M₂.chart_equivariant g hg s.2 hs.2 hgs.2 y ((hE₂ y).mpr hz) hgy)

end Sum

end GroupApproximation
