import GroupApproximation.CharClass.OddPEval
import GroupApproximation.CharClass.SteenrodCochain

/-!
# Evaluating graded cochains on the full tuple model

The Cartan comparison at odd `p` compares two chain maps into the `2p`-fold tensor power of the
singular chains, and every chain-level identity it needs is checked by evaluation.  Two elements
of the full model `tupAllMod K X r` are equal as soon as every tuple of homogeneous graded cochains
gives them the same value: the indicator cochains of a tuple's slots already read off that
tuple's coefficient.

The evaluation of a boundary is the transpose of the differential.  On a functional whose slot `j`
is concentrated in degree `d j`, only tuples of exactly those degrees survive, so the Koszul prefix
sign of the tuple is the prefix sign of the prescribed degrees, a constant.

## Main results

* `tupEvalAll` — the evaluation of `r` graded cochains on the full model, with no sign.
* `tupEvalAll_tupIncl` — on the degree-`k` carrier it is `tupEval`.
* `tagIndicator`, `isHomogFun_tagIndicator` — the indicator cochain of a tagged simplex.
* `tupAllMod_eq_of_eval` — **homogeneous functionals separate the full model.**
* `tupEvalAll_tupDAll` — **the evaluation of a boundary**, on homogeneous functionals.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

-- `TagSimp X` and `TupAll X r` carry no decidable equality (a simplex is a continuous map), so the
-- indicator's `if` and `Finsupp.single_apply` need the classical instance.  It is `low` priority, so
-- the `Fin` instances used by `Function.update` and the prefix sums still win.
open scoped Classical

variable (K : Type) [CommRing K] {X : TopCat.{0}} {r : ℕ}

/-! ## 1. The evaluation -/

/-- **The evaluation of `r` graded cochains on the full model**: on a basis tuple, the product of
the slot evaluations, with no sign. -/
def tupEvalAll (X : TopCat.{0}) (r : ℕ) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) :
    tupAllMod K X r →ₗ[K] K :=
  Finsupp.linearCombination K (fun t : TupAll X r => ∏ j, tagEvalG K (φ j) (t j))

theorem tupEvalAll_single (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (t : TupAll X r) :
    tupEvalAll K X r φ (Finsupp.single t (1 : K)) = ∏ j, tagEvalG K (φ j) (t j) := by
  rw [tupEvalAll, Finsupp.linearCombination_single, one_smul]

/-- On the degree-`k` carrier the evaluation is `tupEval`. -/
theorem tupEvalAll_tupIncl (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ)
    (x : tupMod K X r k) : tupEvalAll K X r φ (tupIncl K X r k x) = tupEval K X r k φ x := by
  have h : (tupEvalAll K X r φ).comp (tupIncl K X r k) = tupEval K X r k φ := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupIncl_single, tupEvalAll_single, tupEval_single]
  exact LinearMap.congr_fun h x

/-! ## 2. Homogeneous functionals, and the indicators that separate -/

/-- The graded cochains `φ` are concentrated, slot by slot, in the degrees `d`. -/
def IsHomogFun (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (d : Fin r → ℕ) : Prop :=
  ∀ j n, n ≠ d j → φ j n = 0

open Classical in
/-- **The indicator cochain of a tagged simplex**: `1` on that simplex and `0` on every other
simplex of every degree.  Singular simplices have no decidable equality, so the test is
classical. -/
def tagIndicator (τ : TagSimp X) : ∀ n : ℕ, singularCochainGroup K X n :=
  fun n => cochainOfFun n (fun σ => if (⟨n, σ⟩ : TagSimp X) = τ then (1 : K) else 0)

open Classical in
theorem tagEvalG_tagIndicator (τ τ' : TagSimp X) :
    tagEvalG K (tagIndicator K τ) τ' = if τ' = τ then 1 else 0 := by
  unfold tagEvalG tagIndicator
  rw [cochainEval_cochainOfFun]

open Classical in
/-- The indicators of a tuple's slots are concentrated in that tuple's degrees. -/
theorem isHomogFun_tagIndicator (t : TupAll X r) :
    IsHomogFun K (fun j => tagIndicator K (t j)) (fun j => (t j).1) := by
  intro j n hn
  apply cochain_ext
  intro σ
  show cochainEval n (cochainOfFun n
      (fun σ' => if (⟨n, σ'⟩ : TagSimp X) = t j then (1 : K) else 0)) σ = cochainEval n 0 σ
  rw [cochainEval_cochainOfFun, cochainEval_zero, if_neg]
  intro h
  exact hn (congrArg Sigma.fst h)

/-- Evaluating against the indicators of a tuple's slots reads off that tuple's coefficient. -/
theorem tupEvalAll_tagIndicator (t : TupAll X r) (z : tupAllMod K X r) :
    tupEvalAll K X r (fun j => tagIndicator K (t j)) z = z t := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.zero_apply]
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.add_apply]
  | single s a =>
    have hs : Finsupp.single s a = a • Finsupp.single s (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, tupEvalAll_single, Finsupp.smul_apply, Finsupp.single_apply]
    simp only [tagEvalG_tagIndicator, smul_eq_mul]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg hst, mul_zero]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hst
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj), mul_zero]

/-- **Homogeneous functionals separate the full model.** -/
theorem tupAllMod_eq_of_eval {x y : tupAllMod K X r}
    (h : ∀ (d : Fin r → ℕ) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n),
      IsHomogFun K φ d → tupEvalAll K X r φ x = tupEvalAll K X r φ y) : x = y := by
  ext t
  rw [← tupEvalAll_tagIndicator K t x, ← tupEvalAll_tagIndicator K t y]
  exact h _ _ (isHomogFun_tagIndicator K t)

/-! ## 3. The evaluation of a boundary -/

/-- A tuple of total degree `0` has no boundary. -/
theorem tupDAll_single_of_tot_eq_zero (t : TupAll X r) (ht : ∑ j, (t j).1 = 0) :
    tupDAll K X r (Finsupp.single t (1 : K)) = 0 := by
  rw [tupDAll, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [slotBd_single, slotBdGen]
  have hj : (t j).1 = 0 := by
    have hle : (t j).1 ≤ ∑ l, (t l).1 :=
      Finset.single_le_sum (f := fun l => (t l).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have key : ∀ τ : TagSimp X, τ.1 = 0 →
      Finsupp.linearCombination K
          (fun τ' : TagSimp X => Finsupp.single (Function.update t j τ') (1 : K)) (tagBd K X τ)
        = 0 := by
    rintro ⟨n, σ⟩ hn
    simp only at hn
    subst hn
    rw [tagBd_zero, map_zero]
  rw [key (t j) hj, smul_zero]

/-- **The evaluation of the boundary of one tuple**, on a homogeneous functional. -/
theorem tupEvalAll_tupDAll_single (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (d : Fin r → ℕ) (hφ : IsHomogFun K φ d) (t : TupAll X r) :
    tupEvalAll K X r φ (tupDAll K X r (Finsupp.single t (1 : K)))
      = ∑ j : Fin r, (-1 : K) ^ (∑ l ∈ Finset.Iio j, d l) *
          ∏ l, tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t l) := by
  rcases Nat.eq_zero_or_pos (∑ j, (t j).1) with h0 | hpos
  · rw [tupDAll_single_of_tot_eq_zero K t h0, map_zero]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have hj : (t j).1 = 0 := by
      have hle : (t j).1 ≤ ∑ l, (t l).1 :=
        Finset.single_le_sum (f := fun l => (t l).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    have hz : tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) j) (t j) = 0 := by
      rw [Function.update_self]
      refine tagEvalG_of_eq_zero K _ (t j) ?_
      rw [hj, gCoboundary_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]
  · obtain ⟨k, hk⟩ : ∃ k, ∑ j, (t j).1 = k + 1 := ⟨∑ j, (t j).1 - 1, by omega⟩
    have hincl : Finsupp.single t (1 : K)
        = tupIncl K X r (k + 1) (Finsupp.single (⟨t, hk⟩ : TupIdx X r (k + 1)) (1 : K)) :=
      (tupIncl_single K X (k + 1) ⟨t, hk⟩).symm
    rw [hincl, ← LinearMap.comp_apply (tupDAll K X r) (tupIncl K X r (k + 1)),
      ← tupIncl_comp_tupD K X k, LinearMap.comp_apply, tupEvalAll_tupIncl, tupEval_tupD_single]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hall : ∀ l ∈ Finset.Iio j, (t l).1 = d l
    · have hpre : tupPre t j = ∑ l ∈ Finset.Iio j, d l := Finset.sum_congr rfl hall
      rw [hpre]
    · obtain ⟨l, hl, hne⟩ := not_forall₂.mp hall
      have hlj : l ≠ j := ne_of_lt (Finset.mem_Iio.mp hl)
      have hz : tagEvalG K (Function.update φ j (gCoboundary K X (φ j)) l) (t l) = 0 := by
        rw [Function.update_of_ne hlj]
        exact tagEvalG_of_eq_zero K _ (t l) (hφ l _ hne)
      rw [Finset.prod_eq_zero (Finset.mem_univ l) hz, mul_zero, mul_zero]

/-- **The evaluation of a boundary**, on a homogeneous functional: the Koszul prefix sign of the
prescribed degrees times the evaluation with one slot's cochain replaced by its graded
coboundary. -/
theorem tupEvalAll_tupDAll (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (d : Fin r → ℕ)
    (hφ : IsHomogFun K φ d) (x : tupAllMod K X r) :
    tupEvalAll K X r φ (tupDAll K X r x)
      = ∑ j : Fin r, (-1 : K) ^ (∑ l ∈ Finset.Iio j, d l) *
          tupEvalAll K X r (Function.update φ j (gCoboundary K X (φ j))) x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero, Finset.sum_const_zero]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_add, mul_add]
  | single t a =>
    have hs : Finsupp.single t a = a • Finsupp.single t (1 : K) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, map_smul, smul_eq_mul, tupEvalAll_tupDAll_single K φ d hφ t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, tupEvalAll_single]
    ring

/-- **Cocycles evaluate to zero on boundaries**, on the full model. -/
theorem tupEvalAll_tupDAll_eq_zero (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n)
    (d : Fin r → ℕ) (hφ : IsHomogFun K φ d) (hδ : ∀ j, gCoboundary K X (φ j) = 0)
    (x : tupAllMod K X r) : tupEvalAll K X r φ (tupDAll K X r x) = 0 := by
  rw [tupEvalAll_tupDAll K φ d hφ x]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hupd : Function.update φ j (gCoboundary K X (φ j)) = Function.update φ j 0 := by
    rw [hδ j]
  have hz : tupEvalAll K X r (Function.update φ j 0) = 0 := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply]
    rw [tupEvalAll_single]
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [Function.update_self]
    exact tagEvalG_zero K (t j)
  rw [hupd, hz, LinearMap.zero_apply, mul_zero]

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms tupAllMod_eq_of_eval
#audit_axioms tupEvalAll_tupDAll
#audit_axioms tupEvalAll_tupDAll_eq_zero
