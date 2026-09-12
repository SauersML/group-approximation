import GroupApproximation.Manuscript.NonMF.GerasimovaOsinTheorem11Slice
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# On a free subsemigroup the `ℓ²`-norm is multiplicative

Dykema–Haagerup–Rørdam (Duke Math. J. 90 (1997), §1, equation (1.1)) and Dykema–de la
Harpe (J. Math. Pures Appl. 78 (1999)): if a finite set `T ⊆ G` freely generates a free
subsemigroup and `a = ∑_{g ∈ T} c(g) λ(g)`, then distinct words in `T` have distinct
products, so `‖aⁿ‖₂ = ‖a‖₂ⁿ` and `r₂(a) = ‖a‖₂`.

The proof tracks the vector `aⁿδ₁ ∈ ℓ²(G)` instead of expanding `aⁿ` as a sum over
words:

* `aⁿ⁺¹δ₁ = ∑_{g ∈ T} c(g) ρ(g)(aⁿδ₁)`, where `ρ` is the right regular representation
  (`mul_translationSum_deltaOne`, from `ReducedGroupCStarTrace.apply_single`);
* `aⁿδ₁` vanishes off the products of words of length `n` in `T`
  (`pow_translationSum_deltaOne_support`);
* for `g ≠ g'` in `T` the translates `ρ(g)(aⁿδ₁)` and `ρ(g')(aⁿδ₁)` have disjoint
  supports, since a word of length `n + 1` determines its last letter; Pythagoras gives
  `‖aⁿ⁺¹δ₁‖² = (∑_g |c(g)|²)·‖aⁿδ₁‖²` (`reducedTwoNorm_pow_sq_of_free`).

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (stable rank one, the Dykema–de la Harpe
criterion behind Gerasimova–Osin's Theorem 1.1).  Certifies no printed sentence on its
own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreePrinted

open GroupApproximation.ReducedGroupCStarTrace
open Filter
open scoped InnerProductSpace

universe u

variable {G : Type u} [Group G]

/-- The translation sum `∑_{g ∈ T} c(g) λ(g)` in `C*_r(G)`. -/
noncomputable def translationSum (T : Finset G) (c : G → ℂ) : ReducedGroupCStar G :=
  ∑ g ∈ T, c g • reducedLeftRegular G g

/-- Pythagoras for a finite family with pairwise vanishing inner products. -/
theorem norm_sum_sq_of_pairwise_inner_eq_zero {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (s : Finset ι) (v : ι → E)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪v i, v j⟫_ℂ = 0 := fun i hi j hj hij =>
      h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hperp : ⟪v a, ∑ j ∈ s, v j⟫_ℂ = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun j hj =>
        h a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (fun e => ha (e ▸ hj))
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sq,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hperp, ← sq, ← sq, ih hs]

/-- The identity column of `W · translationSum T c` combines right translates of the
identity column of `W`. -/
theorem mul_translationSum_deltaOne (W : ReducedGroupCStar G) (T : Finset G) (c : G → ℂ) :
    ((W * translationSum T c : ReducedGroupCStar G) : GroupHilbert G →L[ℂ] GroupHilbert G)
        (deltaOne G)
      = ∑ g ∈ T, c g • rightRegularOperator G g
          ((W : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) := by
  rw [MulMemClass.coe_mul, mul_apply_eq_comp, translationSum,
    AddSubmonoidClass.coe_finsetSum, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [SetLike.val_smul, smul_apply, map_smul]
  congr 1
  rw [reducedLeftRegular_deltaOne]
  have h := apply_single G W g 1
  rw [one_smul] at h
  convert h using 3

/-- The right translations are isometries of `ℓ²(G)`. -/
theorem norm_rightRegularOperator_apply (g : G) (V : GroupHilbert G) :
    ‖rightRegularOperator G g V‖ = ‖V‖ :=
  (rightRegular G g).norm_map V

open Classical in
/-- The coordinates of the identity point mass. -/
theorem deltaOne_apply (x : G) : deltaOne G x = if x = 1 then 1 else 0 := by
  classical
  unfold deltaOne
  rw [lp.coeFn_single]
  simp [Pi.single_apply]

/-- Products of words of length `n` with letters in `T`. -/
def wordProducts (T : Set G) (n : ℕ) : Set G :=
  {x | ∃ w : List G, w.length = n ∧ (∀ z ∈ w, z ∈ T) ∧ w.prod = x}

/-- **`aⁿδ₁` vanishes off the products of words of length `n`.** -/
theorem pow_translationSum_deltaOne_support (T : Finset G) (c : G → ℂ) (n : ℕ) :
    ∀ x, x ∉ wordProducts (T : Set G) n →
      ((translationSum T c ^ n : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G) x = 0 := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, OneMemClass.coe_one, one_apply_eq_self, deltaOne_apply, if_neg]
    rintro rfl
    exact hx ⟨[], rfl, by simp, rfl⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ, mul_translationSum_deltaOne, lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun g hg => ?_
    rw [lp.coeFn_smul, Pi.smul_apply, rightRegularOperator_apply, ih, smul_zero]
    rintro ⟨w, hlen, hmem, hprod⟩
    refine hx ⟨w ++ [g], by simp [hlen], ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hmem z hz
      · rw [List.mem_singleton.mp hz]
        exact Finset.mem_coe.mpr hg
    · rw [List.prod_append, hprod, List.prod_singleton, inv_mul_cancel_right]

/-- **`‖aⁿ‖₂² = (∑_{g ∈ T} |c(g)|²)ⁿ` on a free subsemigroup.** -/
theorem reducedTwoNorm_pow_sq_of_free (T : Finset G) (c : G → ℂ)
    (hfree : FreelyGeneratesFreeSubsemigroup (T : Set G)) (n : ℕ) :
    reducedTwoNorm (translationSum T c ^ n) ^ 2 = (∑ g ∈ T, ‖c g‖ ^ 2) ^ n := by
  unfold reducedTwoNorm
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, OneMemClass.coe_one, one_apply_eq_self,
      GroupVonNeumann.norm_deltaOne, one_pow]
  | succ n ih =>
    have hsupp := pow_translationSum_deltaOne_support T c n
    rw [pow_succ (translationSum T c) n, mul_translationSum_deltaOne, norm_sum_sq_of_pairwise_inner_eq_zero]
    · rw [Finset.sum_congr rfl fun g _ => by
          rw [norm_smul, mul_pow, norm_rightRegularOperator_apply],
        ← Finset.sum_mul, ih, pow_succ, mul_comm]
    · intro g hg g' hg' hne
      rw [inner_smul_left, inner_smul_right, lp.inner_eq_tsum]
      have hzero : ∀ x : G,
          ⟪(rightRegularOperator G g
              (((translationSum T c ^ n : ReducedGroupCStar G) :
                GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))) x,
            (rightRegularOperator G g'
              (((translationSum T c ^ n : ReducedGroupCStar G) :
                GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G))) x⟫_ℂ = 0 := by
        intro x
        rw [rightRegularOperator_apply, rightRegularOperator_apply]
        by_cases h1 : x * g⁻¹ ∈ wordProducts (T : Set G) n
        · by_cases h2 : x * g'⁻¹ ∈ wordProducts (T : Set G) n
          · exfalso
            obtain ⟨w, -, hwm, hwp⟩ := h1
            obtain ⟨w', -, hwm', hwp'⟩ := h2
            have hmem : ∀ (l : List G) (a : G), (∀ z ∈ l, z ∈ (T : Set G)) → a ∈ T →
                ∀ z ∈ l ++ [a], z ∈ (T : Set G) := by
              intro l a hl ha z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact hl z hz
              · rw [List.mem_singleton.mp hz]
                exact Finset.mem_coe.mpr ha
            have heq := hfree (w ++ [g]) (w' ++ [g']) (hmem w g hwm hg) (hmem w' g' hwm' hg')
              (by simp) (by simp) (by
                rw [List.prod_append, List.prod_append, hwp, hwp', List.prod_singleton,
                  List.prod_singleton, inv_mul_cancel_right, inv_mul_cancel_right])
            exact hne (by simpa using congrArg List.getLast? heq)
          · rw [hsupp _ h2, inner_zero_right]
        · rw [hsupp _ h1, inner_zero_left]
      simp only [hzero, tsum_zero, mul_zero]

theorem reducedTwoNorm_translationSum_pow_of_free (T : Finset G) (c : G → ℂ)
    (hfree : FreelyGeneratesFreeSubsemigroup (T : Set G)) (n : ℕ) :
    reducedTwoNorm (translationSum T c ^ n) = reducedTwoNorm (translationSum T c) ^ n := by
  have h1 := reducedTwoNorm_pow_sq_of_free T c hfree n
  have h2 := reducedTwoNorm_pow_sq_of_free T c hfree 1
  rw [pow_one, pow_one] at h2
  rw [← Real.sqrt_sq (reducedTwoNorm_nonneg (translationSum T c ^ n)), h1, ← h2,
    pow_right_comm, Real.sqrt_sq (pow_nonneg (reducedTwoNorm_nonneg _) n)]

/-- **`r₂(a) = ‖a‖₂` on a free subsemigroup.** -/
theorem l2SpectralRadius_translationSum_of_free (T : Finset G) (c : G → ℂ)
    (hfree : FreelyGeneratesFreeSubsemigroup (T : Set G)) :
    l2SpectralRadius (translationSum T c) = reducedTwoNorm (translationSum T c) := by
  rw [l2SpectralRadius]
  have hev : ∀ᶠ k : ℕ in atTop,
      reducedTwoNorm (translationSum T c ^ k) ^ ((k : ℝ)⁻¹)
        = reducedTwoNorm (translationSum T c) := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [reducedTwoNorm_translationSum_pow_of_free T c hfree k,
      Real.pow_rpow_inv_natCast (reducedTwoNorm_nonneg _) (by omega)]
  rw [Filter.limsup_congr hev, limsup_const]

/-- Left translation does not move the `ℓ²`-norm. -/
theorem reducedTwoNorm_leftRegular_mul (t : G) (x : ReducedGroupCStar G) :
    reducedTwoNorm (reducedLeftRegular G t * x) = reducedTwoNorm x := by
  rw [reducedTwoNorm, reducedTwoNorm, MulMemClass.coe_mul, mul_apply_eq_comp]
  exact (GroupApproximation.ReducedGroupCStarTrace.leftRegular G t).norm_map _

/-- `λ(t) · ∑_{g ∈ F} c(g) λ(g) = ∑_{h ∈ tF} c(t⁻¹h) λ(h)`. -/
theorem leftRegular_mul_translationSum [DecidableEq G] (t : G) (F : Finset G) (c : G → ℂ) :
    reducedLeftRegular G t * translationSum F c
      = translationSum (F.image fun g => t * g) (fun h => c (t⁻¹ * h)) := by
  rw [translationSum, translationSum, Finset.mul_sum,
    Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, ← reducedLeftRegular_mul, inv_mul_cancel_left]

/-- A combination indexed by `Fin m`, regrouped along the distinct group elements. -/
theorem finSum_eq_translationSum [DecidableEq G] {m : ℕ} (c : Fin m → ℂ) (γ : Fin m → G) :
    ∑ i : Fin m, c i • reducedLeftRegular G (γ i)
      = translationSum (Finset.univ.image γ)
          (fun g => ∑ i ∈ Finset.univ.filter (fun i => γ i = g), c i) := by
  rw [translationSum]
  simp only [Finset.sum_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image γ)
    (g := γ) (fun i _ => Finset.mem_image_of_mem γ (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

end TorsionFreePrinted
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted

#audit_axioms norm_sum_sq_of_pairwise_inner_eq_zero
#audit_axioms mul_translationSum_deltaOne
#audit_axioms pow_translationSum_deltaOne_support
#audit_axioms reducedTwoNorm_pow_sq_of_free
#audit_axioms l2SpectralRadius_translationSum_of_free
#audit_axioms leftRegular_mul_translationSum
#audit_axioms finSum_eq_translationSum
