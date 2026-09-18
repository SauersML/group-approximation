import GroupApproximation.Manuscript.NonMF.Full.NM16.BKLocalization
import GroupApproximation.Manuscript.NonMF.Full.NM16.BKUnitalized
import GroupApproximation.Analysis.BlackadarKirchbergMFUCPApproximateInverse
import GroupApproximation.Analysis.BlackadarKirchbergAbstractFiniteDimensionalLift
import GroupApproximation.Analysis.BlackadarKirchbergCoordinateSelection
import GroupApproximation.Analysis.NFAlgebra
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): nuclear and MF implies NF

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310--315 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module proves the converse half for unital C-star algebras with no
hypothesis beyond nuclearity and MF. The localization step is the theorem
`coronaUCPFiniteCoordinateLocalization` from `Full/NM16/BKLocalization`. Lane NM16
duplicates the foreign `NonMF/RelatedBK/ConverseReduction` here, and removes its
`hloc` hypothesis by applying that theorem.

## Proof route

* *Trivial algebra.* If `A` is a subsingleton, the zero maps into `M_1` are an
  NF approximation, because every norm in `A` vanishes.
* *Nontrivial algebra* (`hasLocalNFApproximation_of_nuclear_of_mf`).
  Fix `F` and `ε`, and let `C` bound the norms on `F`. Choose `0 < δ ≤ 1/2`
  with `4 (1 + C)² δ < ε`. Let `S` be `F` together with its pairwise products.
  1. `exists_ucp_cpc_finiteDimensional_approximation` gives a UCP `α : A → D`
     and a CPC `β : D → A` with `‖β α s - s‖ ≤ δ (1 + ‖s‖)` on `S`.
  2. The MF corona embedding gives a unital `π : A → Q(X)` and a UCP
     `Ext : Q(X) → D` with `Ext ∘ π = α`.
  3. The CPC map `π ∘ β` has a CPC lift `L : D → ∏ M_{X n}`. Hence
     `Ext (mk (L d)) = α (β d)`.
  4. For `a, b ∈ F`, the corona image of `L α(ab) - L α a · L α b` is
     `π(β α(ab) - β α a · β α b)`. By `norm_mul_defect_le_of_approx`, its norm
     is `< ε`. So some tail `n ≥ N` has every coordinate norm `< ε`.
  5. Localize at the finite set `{L α a : a ∈ F}` with tolerance `δ` and
     threshold `N`. This gives `ρ` and `θ`.
  6. Put `down = ρ ∘ L ∘ α` and `up = β ∘ θ`. The multiplicative defect of
     `down` is `ρ` applied to a sequence whose tail is `< ε`. The recovery
     error splits into three pieces of sizes `δ`, `δ (1 + C)` and `δ (1 + C)`.
-/

namespace GroupApproximation.Full.NM16

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-- Bounded matrix sequences form a C-star algebra. -/
local instance boundedMatrixSequenceCStarAlgebraForRelatedBKNM16
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (BoundedMatrixSequence (fun n ↦ X n)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForRelatedBKNM16
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- A subsingleton C-star algebra has NF approximations through `M_1`, given by
zero maps. -/
theorem hasLocalNFApproximation_of_subsingleton
    {A : Type u} [CStarAlgebra A] [Subsingleton A]
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    HasLocalNFApproximation A F ε := by
  let Y : FiniteModel := ⟨Fin 1, inferInstance, inferInstance⟩
  have hY : Nonempty Y := ⟨(0 : Fin 1)⟩
  refine ⟨Y, hY, ?_⟩
  letI : Nonempty Y := hY
  have hnorm : ∀ x : A, ‖x‖ = 0 := fun x ↦ by
    rw [Subsingleton.elim x 0, norm_zero]
  refine ⟨0, 0, BlackadarKirchberg.isCompletelyPositive_zero,
    BlackadarKirchberg.isCompletelyPositive_zero, ?_, ?_, ?_, ?_⟩
  · intro a
    rw [LinearMap.zero_apply, norm_zero]
    exact norm_nonneg _
  · intro d
    rw [LinearMap.zero_apply, norm_zero]
    exact norm_nonneg _
  · intro a _ha
    rw [hnorm]
    exact hε.le
  · intro a _ha b _hb
    simp only [LinearMap.zero_apply, mul_zero, sub_zero, norm_zero]
    exact hε.le

/-- **Nuclear plus MF gives local NF approximations.** This is the nontrivial
unital case (tex L310--315). -/
theorem hasLocalNFApproximation_of_nuclear_of_mf
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A)
    (F : Finset A) {ε : ℝ} (hε : 0 < ε) :
    HasLocalNFApproximation A F ε := by
  classical
  -- Constants.
  obtain ⟨C, hC0, hFC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ F, ‖a‖ ≤ C :=
    ⟨∑ b ∈ F, ‖b‖, Finset.sum_nonneg (fun b _ ↦ norm_nonneg b),
      fun a ha ↦ Finset.single_le_sum (f := fun b : A ↦ ‖b‖)
        (fun b _ ↦ norm_nonneg b) ha⟩
  have h1C : 0 < 1 + C := by linarith
  have hK : 0 < 8 * (1 + C) ^ 2 := mul_pos (by norm_num) (pow_pos h1C 2)
  obtain ⟨δ, hδ0, hδhalf, hδε⟩ :
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 4 * (1 + C) ^ 2 * δ < ε := by
    have hpos : 0 < min (1 / 2 : ℝ) (ε / (8 * (1 + C) ^ 2)) :=
      lt_min (by norm_num) (div_pos hε hK)
    have hle : min (1 / 2 : ℝ) (ε / (8 * (1 + C) ^ 2)) * (8 * (1 + C) ^ 2) ≤ ε :=
      (le_div_iff₀ hK).1 (min_le_right _ _)
    refine ⟨min (1 / 2 : ℝ) (ε / (8 * (1 + C) ^ 2)), hpos, min_le_left _ _, ?_⟩
    linarith [mul_pos hpos (pow_pos h1C 2)]
  have hδ1 : δ ≤ 1 := by linarith
  obtain ⟨S, hFS, hprodS⟩ : ∃ S : Finset A,
      (∀ a ∈ F, a ∈ S) ∧ ∀ a ∈ F, ∀ b ∈ F, a * b ∈ S :=
    ⟨F ∪ (F ×ˢ F).image (fun p : A × A ↦ p.1 * p.2),
      fun a ha ↦ Finset.mem_union_left _ ha,
      fun a ha b hb ↦ Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩)⟩
  -- Step 1: unital nuclear approximation.
  obtain ⟨D, hDnt, α, β, hαCP, hαOne, hβCP, hβContract, hαβ⟩ :=
    exists_ucp_cpc_finiteDimensional_approximation hnuc S hδ0 (by linarith)
  letI : Nontrivial D := hDnt
  have hαContract : ∀ a : A, ‖α a‖ ≤ ‖a‖ := fun a ↦
    BlackadarKirchberg.norm_apply_le_of_ucp_finiteDimensionalTarget
      α hαCP hαOne a
  have happrox : ∀ a ∈ F, ‖β (α a) - a‖ ≤ δ * (1 + C) := fun a ha ↦
    (hαβ a (hFS a ha)).trans
      (mul_le_mul_of_nonneg_left (by linarith [hFC a ha]) hδ0.le)
  -- Step 2: MF corona embedding with a UCP extension of `α`.
  obtain ⟨X, hXne, π, Ext, _hπinj, hExtCP, hExtOne, hExtπ⟩ :=
    BlackadarKirchberg.exists_unitalMFEmbedding_with_ucp_extension
      hMF α hαCP hαOne
  letI : ∀ n, Nonempty (X n) := hXne
  let πL : A →ₗ[ℂ] NormMatrixCStarCorona (fun n ↦ X n) :=
    { toFun := π
      map_add' := fun x y ↦ map_add π x y
      map_smul' := fun c x ↦ map_smul π c x }
  have hπLCP : IsCompletelyPositive πL := by
    intro n M hM
    exact (isCompletelyPositive_of_starAlgHom π.toNonUnitalStarAlgHom) n M hM
  have hπContract : ∀ a : A, ‖π a‖ ≤ ‖a‖ := fun a ↦
    NonUnitalStarAlgHom.norm_apply_le π a
  -- Step 3: CPC lift of `π ∘ β`.
  obtain ⟨L, hLCP, hLContract, hLmk⟩ :=
    BlackadarKirchberg.exists_completelyPositiveContractive_finiteDimensional_lift
      (X := fun n ↦ X n) (πL.comp β) (hπLCP.comp hβCP)
      (fun d ↦ (hπContract (β d)).trans (hβContract d))
  have hLmk' : ∀ d : D,
      normMatrixCStarCoronaMk (fun n ↦ X n) (L d) = π (β d) := fun d ↦ hLmk d
  -- Step 4: the corona multiplicative defect and a good tail.
  have hdefect : ∀ a ∈ F, ∀ b ∈ F,
      ‖normMatrixCStarCoronaMk (fun n ↦ X n)
          (L (α (a * b)) - L (α a) * L (α b))‖ < ε := by
    intro a ha b hb
    have hmk : normMatrixCStarCoronaMk (fun n ↦ X n)
        (L (α (a * b)) - L (α a) * L (α b)) =
          π (β (α (a * b)) - β (α a) * β (α b)) := by
      rw [map_sub (normMatrixCStarCoronaMk (fun n ↦ X n)),
        map_mul (normMatrixCStarCoronaMk (fun n ↦ X n)),
        hLmk', hLmk', hLmk', map_sub π, map_mul π]
    have hab : ‖a * b‖ ≤ C * C :=
      (norm_mul_le a b).trans (mul_le_mul (hFC a ha) (hFC b hb) (norm_nonneg b) hC0)
    have hw : ‖β (α (a * b)) - a * b‖ ≤ δ * (1 + C * C) :=
      (hαβ (a * b) (hprodS a ha b hb)).trans
        (mul_le_mul_of_nonneg_left (by linarith [hab]) hδ0.le)
    rw [hmk]
    exact lt_of_le_of_lt ((hπContract _).trans
      (norm_mul_defect_le_of_approx a b (β (α a)) (β (α b)) (β (α (a * b)))
        hδ0.le hδ1 hC0 (hFC a ha) (hFC b hb) (happrox a ha) (happrox b hb) hw))
      hδε
  have hev : ∀ᶠ n in Filter.atTop, ∀ p ∈ F ×ˢ F,
      ‖(L (α (p.1 * p.2)) - L (α p.1) * L (α p.2)) n‖ < ε :=
    (Filter.eventually_all_finset (F ×ˢ F)
      (p := fun p n ↦ ‖(L (α (p.1 * p.2)) - L (α p.1) * L (α p.2)) n‖ < ε)).2
      (fun p hp ↦ BlackadarKirchberg.eventually_coord_norm_lt_of_corona_norm_lt _
        (hdefect p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  -- Step 5: localization.
  obtain ⟨Y, hY, ρ, θ, hρtail, hθCP, hθContract, hθρ⟩ :=
    coronaUCPFiniteCoordinateLocalization X D Ext hExtCP hExtOne (F.image (fun a ↦ L (α a))) δ hδ0 N
  letI : Nonempty Y := hY
  let ρL : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] Matrix Y Y ℂ :=
    { toFun := ρ
      map_add' := fun x y ↦ map_add ρ x y
      map_smul' := fun c x ↦ map_smul ρ c x }
  have hρLCP : IsCompletelyPositive ρL := by
    intro n M hM
    exact (isCompletelyPositive_of_starAlgHom ρ) n M hM
  have hρContract : ∀ x : BoundedMatrixSequence (fun n ↦ X n), ‖ρ x‖ ≤ ‖x‖ :=
    fun x ↦ hρtail x ‖x‖
      (fun n _ ↦ boundedMatrixSequence_coord_norm_le (fun n ↦ X n) x n)
  -- Step 6: assemble.
  refine ⟨Y, hY, ?_⟩
  refine ⟨ρL.comp (L.comp α), β.comp θ, hρLCP.comp (hLCP.comp hαCP),
    hβCP.comp hθCP, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hρContract _).trans ((hLContract _).trans (hαContract a))
  · intro d
    exact (hβContract _).trans (hθContract d)
  · intro a ha
    change ‖β (θ (ρ (L (α a)))) - a‖ ≤ ε
    have hT : L (α a) ∈ F.image (fun a ↦ L (α a)) :=
      Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hExtmk : Ext (normMatrixCStarCoronaMk (fun n ↦ X n) (L (α a))) =
        α (β (α a)) := by
      rw [hLmk' (α a)]
      exact hExtπ (β (α a))
    have hloc1 : ‖θ (ρ (L (α a))) - α (β (α a))‖ ≤ δ := by
      calc
        ‖θ (ρ (L (α a))) - α (β (α a))‖ =
            ‖θ (ρ (L (α a))) -
              Ext (normMatrixCStarCoronaMk (fun n ↦ X n) (L (α a)))‖ := by
          rw [hExtmk]
        _ ≤ δ := hθρ _ hT
    have hsplit : β (θ (ρ (L (α a)))) - a =
        β (θ (ρ (L (α a))) - α (β (α a))) + β (α (β (α a) - a)) +
          (β (α a) - a) := by
      rw [map_sub β, map_sub α, map_sub β]
      abel
    have hb1 : ‖β (θ (ρ (L (α a))) - α (β (α a)))‖ ≤ δ :=
      (hβContract _).trans hloc1
    have hb2 : ‖β (α (β (α a) - a))‖ ≤ δ * (1 + C) :=
      (hβContract _).trans ((hαContract _).trans (happrox a ha))
    have h3 := norm_add_le
      (β (θ (ρ (L (α a))) - α (β (α a))) + β (α (β (α a) - a))) (β (α a) - a)
    have h4 := norm_add_le
      (β (θ (ρ (L (α a))) - α (β (α a)))) (β (α (β (α a) - a)))
    rw [hsplit]
    linarith [happrox a ha, mul_nonneg hδ0.le hC0,
      mul_nonneg (mul_nonneg hδ0.le hC0) hC0]
  · intro a ha b hb
    change ‖ρ (L (α (a * b))) - ρ (L (α a)) * ρ (L (α b))‖ ≤ ε
    rw [← map_mul ρ, ← map_sub ρ]
    exact hρtail _ ε
      (fun n hn ↦ (hN n hn (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩)).le)

/-- **Nuclear and MF implies NF** (tex L310--315). This covers unital C-star
algebras. The separability part of NF is the separability part of MF. -/
theorem isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra
    {A : Type u} [CStarAlgebra A]
    (hnuc : IsNuclearCStarAlgebra A) (hMF : IsMFAlgebra A) :
    IsNFAlgebra A := by
  refine ⟨hMF.1, fun F ε hε ↦ ?_⟩
  rcases subsingleton_or_nontrivial A with _hA | _hA
  · exact hasLocalNFApproximation_of_subsingleton F hε
  · exact hasLocalNFApproximation_of_nuclear_of_mf hnuc hMF F hε

end

end GroupApproximation.Full.NM16

open GroupApproximation.Full.NM16

#audit_axioms hasLocalNFApproximation_of_subsingleton
#audit_axioms hasLocalNFApproximation_of_nuclear_of_mf
#audit_axioms isNFAlgebra_of_isNuclearCStarAlgebra_of_isMFAlgebra
