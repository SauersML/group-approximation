import GroupApproximation.Sofic.Sofic

/-!
# The permutation layer of a wreath model

Section 29.4 of the dossier: a family of fibre permutations `Θ : A → Sym(D)`
together with a base permutation `σ` of `A` acts on `D × A` by

`(d, a) ↦ (Θ (σ a) d, σ a)`.

In the wreath model `Θ a` is the approximate lamp permutation labelled by the
base point `a`; taking `Θ` constant recovers the product of two models.

Everything the wreath soficity proof needs about this layer follows from one
exact formula: the normalized Hamming distance between two such permutations is
the average over base points of the fibre distances, a base point whose images
differ contributing a whole fibre.  Multiplicativity and separation estimates
for the wreath model both drop out of it.
-/

namespace GroupApproximation

namespace WreathLayer

universe u

/-- The product of two finite models. -/
@[reducible] def prodModel (D A : FiniteModel) : FiniteModel where
  carrier := D.carrier × A.carrier
  fintype := inferInstance
  decidableEq := inferInstance

variable {D A : FiniteModel}

/-- The permutation of `D × A` that moves the base point by `σ` and acts in the
fibre by the permutation labelling the *target* base point. -/
def fiberPerm (Θ : A → Equiv.Perm D) (σ : Equiv.Perm A) :
    Equiv.Perm (prodModel D A) where
  toFun p := (Θ (σ p.2) p.1, σ p.2)
  invFun p := ((Θ p.2)⁻¹ p.1, σ⁻¹ p.2)
  left_inv := fun p => Prod.ext (by simp) (by simp)
  right_inv := fun p => Prod.ext (by simp) (by simp)

@[simp] theorem fiberPerm_apply (Θ : A → Equiv.Perm D) (σ : Equiv.Perm A)
    (p : prodModel D A) : fiberPerm Θ σ p = (Θ (σ p.2) p.1, σ p.2) := rfl

/-- Composition of two such permutations is again one, with the fibre labels
multiplied at the intermediate base point.  No hypothesis is needed: this is an
identity of permutations, not an approximation. -/
theorem fiberPerm_mul (Θ₁ Θ₂ : A → Equiv.Perm D) (σ₁ σ₂ : Equiv.Perm A) :
    fiberPerm Θ₁ σ₁ * fiberPerm Θ₂ σ₂
      = fiberPerm (fun a => Θ₁ a * Θ₂ (σ₁⁻¹ a)) (σ₁ * σ₂) := by
  refine Equiv.ext fun p => ?_
  refine Prod.ext ?_ ?_
  · show Θ₁ (σ₁ (σ₂ p.2)) (Θ₂ (σ₂ p.2) p.1)
      = (Θ₁ ((σ₁ * σ₂) p.2) * Θ₂ (σ₁⁻¹ ((σ₁ * σ₂) p.2))) p.1
    have hbase : (σ₁ * σ₂) p.2 = σ₁ (σ₂ p.2) := rfl
    rw [hbase]
    simp
  · rfl

/-- A product of permutations is the constant-label case. -/
@[simp] theorem fiberPerm_const (p : Equiv.Perm D) (σ : Equiv.Perm A)
    (q : prodModel D A) : fiberPerm (fun _ => p) σ q = (p q.1, σ q.2) := rfl

/-! ## The fibrewise distance formula -/

/-- **The exact fibre average.**  Base points whose images differ contribute a
whole fibre; the others contribute their lamp distance. -/
theorem hammingDistance_fiberPerm (Θ₁ Θ₂ : A → Equiv.Perm D)
    (σ₁ σ₂ : Equiv.Perm A) (hD : 0 < Fintype.card D) :
    hammingDistance (prodModel D A) (fiberPerm Θ₁ σ₁) (fiberPerm Θ₂ σ₂)
      = (∑ a : A, (if σ₁ a = σ₂ a then
            hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1))
        / Fintype.card A := by
  classical
  have hDR : (0 : ℝ) < Fintype.card D := by exact_mod_cast hD
  have hinj : ∀ a : A, Function.Injective (fun d : D => ((d, a) : prodModel D A)) := by
    intro a d d' hdd'
    simpa using congrArg Prod.fst hdd'
  have hval : ∀ (Θ : A → Equiv.Perm D) (σ : Equiv.Perm A) (d : D) (b : A),
      fiberPerm Θ σ ((d, b) : prodModel D A) = (Θ (σ b) d, σ b) :=
    fun _ _ _ _ => rfl
  -- each fibre of the disagreement set, computed exactly
  have hset : ∀ a : A,
      ((hammingDisagreement (fiberPerm Θ₁ σ₁) (fiberPerm Θ₂ σ₂)).filter
        fun p : prodModel D A => p.2 = a)
      = ((Finset.univ.filter fun d : D =>
          ¬ ((Θ₁ (σ₁ a) d = Θ₂ (σ₂ a) d) ∧ σ₁ a = σ₂ a)).image
            (fun d => ((d, a) : prodModel D A))) := by
    intro a
    ext p
    obtain ⟨d, b⟩ := p
    simp only [Finset.mem_filter, mem_hammingDisagreement, hval,
      Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, ne_eq]
    constructor
    · rintro ⟨hne, rfl⟩
      exact ⟨d, hne, rfl, rfl⟩
    · rintro ⟨d', hd', rfl, rfl⟩
      exact ⟨hd', rfl⟩
  have hfiber : (hammingDisagreement (fiberPerm Θ₁ σ₁)
      (fiberPerm Θ₂ σ₂)).card
      = ∑ a : A, (if σ₁ a = σ₂ a then
          (hammingDisagreement (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a))).card
          else Fintype.card D) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun p : prodModel D A => p.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hset a, Finset.card_image_of_injective _ (hinj a)]
    by_cases hcase : σ₁ a = σ₂ a
    · rw [if_pos hcase]
      congr 1
      ext d
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcase, and_true,
        mem_hammingDisagreement, ne_eq]
    · rw [if_neg hcase]
      have huniv : (Finset.univ.filter fun d : D =>
          ¬ ((Θ₁ (σ₁ a) d = Θ₂ (σ₂ a) d) ∧ σ₁ a = σ₂ a))
          = (Finset.univ : Finset D) := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcase,
          and_false, not_false_iff]
      rw [huniv, Finset.card_univ]
  have hcardprod : Fintype.card (prodModel D A)
      = Fintype.card D * Fintype.card A := Fintype.card_prod _ _
  have hcast : ∀ a : A,
      (((if σ₁ a = σ₂ a then
          (hammingDisagreement (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a))).card
          else Fintype.card D) : ℕ) : ℝ) / (Fintype.card D : ℝ)
      = (if σ₁ a = σ₂ a then
          hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1) := by
    intro a
    by_cases hcase : σ₁ a = σ₂ a
    · rw [if_pos hcase, if_pos hcase, hammingDistance]
    · rw [if_neg hcase, if_neg hcase]
      exact div_self hDR.ne'
  rw [hammingDistance, hfiber, hcardprod, Nat.cast_sum, Nat.cast_mul, ← div_div,
    Finset.sum_div]
  exact congrArg (fun s => s / (Fintype.card A : ℝ))
    (Finset.sum_congr rfl fun a _ => hcast a)

/-! ## The two estimates -/

/-- **Multiplicativity estimate.**  Outside a small set of base points the
labellings agree to within `η`, and the whole distance is then within `η` of the
proportion of bad base points. -/
theorem hammingDistance_fiberPerm_le (Θ₁ Θ₂ : A → Equiv.Perm D)
    (σ₁ σ₂ : Equiv.Perm A) (hD : 0 < Fintype.card D) (hA : 0 < Fintype.card A)
    (bad : Finset A) {η : ℝ} (hη : 0 ≤ η)
    (hgood : ∀ a ∉ bad, σ₁ a = σ₂ a ∧
      hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) ≤ η) :
    hammingDistance (prodModel D A) (fiberPerm Θ₁ σ₁) (fiberPerm Θ₂ σ₂)
      ≤ (bad.card : ℝ) / Fintype.card A + η := by
  classical
  have hAR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  rw [hammingDistance_fiberPerm Θ₁ Θ₂ σ₁ σ₂ hD]
  have hterm : ∀ a : A, (if σ₁ a = σ₂ a then
      hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1)
      ≤ (if a ∈ bad then (1 : ℝ) else 0) + η := by
    intro a
    by_cases hb : a ∈ bad
    · rw [if_pos hb]
      by_cases hc : σ₁ a = σ₂ a
      · rw [if_pos hc]
        have := hammingDistance_le_one D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a))
        linarith
      · rw [if_neg hc]
        linarith
    · rw [if_neg hb, zero_add]
      obtain ⟨hc, hle⟩ := hgood a hb
      rw [if_pos hc]
      exact hle
  have hsum : ∑ _a : A, ((if _a ∈ bad then (1 : ℝ) else 0) + η)
      = (bad.card : ℝ) + (Fintype.card A : ℝ) * η := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, Finset.sum_const, Finset.card_univ]
    simp [mul_comm]
  have hbound : ∑ a : A, (if σ₁ a = σ₂ a then
      hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1)
      ≤ (bad.card : ℝ) + (Fintype.card A : ℝ) * η :=
    le_trans (Finset.sum_le_sum fun a _ => hterm a) (le_of_eq hsum)
  rw [div_le_iff₀ hAR]
  calc ∑ a : A, (if σ₁ a = σ₂ a then
        hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1)
      ≤ (bad.card : ℝ) + (Fintype.card A : ℝ) * η := hbound
    _ = ((bad.card : ℝ) / Fintype.card A + η) * Fintype.card A := by
        field_simp

/-- **Separation estimate.**  If outside a small set of base points every fibre
contributes at least `c`, the whole distance is at least `c` times the good
proportion. -/
theorem hammingDistance_fiberPerm_ge (Θ₁ Θ₂ : A → Equiv.Perm D)
    (σ₁ σ₂ : Equiv.Perm A) (hD : 0 < Fintype.card D) (hA : 0 < Fintype.card A)
    (bad : Finset A) {c : ℝ}
    (hgood : ∀ a ∉ bad, c ≤ (if σ₁ a = σ₂ a then
      hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1)) :
    c * (1 - (bad.card : ℝ) / Fintype.card A)
      ≤ hammingDistance (prodModel D A) (fiberPerm Θ₁ σ₁)
          (fiberPerm Θ₂ σ₂) := by
  classical
  have hAR : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  rw [hammingDistance_fiberPerm Θ₁ Θ₂ σ₁ σ₂ hD, le_div_iff₀ hAR]
  have hterm : ∀ a : A, (if a ∈ bad then (0 : ℝ) else c)
      ≤ (if σ₁ a = σ₂ a then
          hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1) := by
    intro a
    by_cases hb : a ∈ bad
    · rw [if_pos hb]
      by_cases hc : σ₁ a = σ₂ a
      · rw [if_pos hc]
        exact hammingDistance_nonnegative _ _ _
      · rw [if_neg hc]
        norm_num
    · rw [if_neg hb]
      exact hgood a hb
  have hsum : ∑ _a : A, (if _a ∈ bad then (0 : ℝ) else c)
      = (Fintype.card A : ℝ) * c - (bad.card : ℝ) * c := by
    have hrw : ∀ a : A, (if a ∈ bad then (0 : ℝ) else c)
        = c - (if a ∈ bad then c else 0) := by
      intro a
      by_cases h : a ∈ bad <;> simp [h]
    rw [Finset.sum_congr rfl fun a _ => hrw a, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      Finset.card_univ]
    simp [mul_comm]
  calc c * (1 - (bad.card : ℝ) / Fintype.card A) * Fintype.card A
      = (Fintype.card A : ℝ) * c - (bad.card : ℝ) * c := by field_simp
    _ = ∑ _a : A, (if _a ∈ bad then (0 : ℝ) else c) := hsum.symm
    _ ≤ ∑ a : A, (if σ₁ a = σ₂ a then
          hammingDistance D (Θ₁ (σ₁ a)) (Θ₂ (σ₂ a)) else 1) :=
        Finset.sum_le_sum fun a _ => hterm a

end WreathLayer

end GroupApproximation
