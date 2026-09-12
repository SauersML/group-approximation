import GroupApproximation.KunThom.CentralizerNormalizationCrossingRepair
import GroupApproximation.Matching.PartialEquivarianceComposition
import GroupApproximation.Sofic.MultiplicativeApproximation
import Mathlib.Algebra.Group.PUnit

/-!
# Two component models as one multiplicative approximation

The relation-improvement theorem `KunThomRounding.exists_pairProduct_relation_eventually`
is stated for a single sequence of finite models.  A composite `f.trans g`
between two components is encoded on the union `X ⊕ Z` of its source and
target component, and a sequence of such pairs with approximate actions on
both summands combines into one `MultiplicativeApproximation`, acting
summandwise.  This file proves the bookkeeping for that packaging:

* normalized disagreement on the union is below `ε` when it is below `ε` on
  both summands;
* the identity is good at every positive level;
* the swap encoding of a composite of two partial bijections has at most the
  four equivariance defects of the factors as bad arcs;
* the labels of the combined approximation are the union labels used by the
  finite repair step.
-/

namespace GroupApproximation
namespace CentralizerNormalizationSumApproximation

open AlmostAutomorphism
open KazhdanImprovement
open FinitePartialBijection
open CentralizerNormalizationCrossingRepair

variable {X Z : FiniteModel}

/-- Disagreement of two summand-preserving permutations splits over the
summands. -/
theorem card_hammingDisagreement_sumCongr (a a' : Equiv.Perm X)
    (b b' : Equiv.Perm Z) :
    (hammingDisagreement (Equiv.sumCongr a b : Equiv.Perm (sumModel X Z))
        (Equiv.sumCongr a' b')).card =
      (hammingDisagreement a a').card + (hammingDisagreement b b').card := by
  classical
  simp only [hammingDisagreement]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Fintype.sum_sum_type]
  simp

/-- Normalized disagreement on the union is below `ε` when it is below `ε` on
both summands. -/
theorem hammingDistance_sumCongr_lt {ε : ℝ} (a a' : Equiv.Perm X)
    (b b' : Equiv.Perm Z)
    (hX : 0 < Fintype.card X) (hZ : 0 < Fintype.card Z)
    (ha : hammingDistance X a a' < ε) (hb : hammingDistance Z b b' < ε) :
    hammingDistance (sumModel X Z) (Equiv.sumCongr a b) (Equiv.sumCongr a' b') <
      ε := by
  unfold hammingDistance at ha hb ⊢
  rw [card_hammingDisagreement_sumCongr]
  have hcard : Fintype.card (sumModel X Z) = Fintype.card X + Fintype.card Z :=
    Fintype.card_sum
  rw [hcard]
  have hXr : (0 : ℝ) < Fintype.card X := by exact_mod_cast hX
  have hZr : (0 : ℝ) < Fintype.card Z := by exact_mod_cast hZ
  rw [div_lt_iff₀ hXr] at ha
  rw [div_lt_iff₀ hZr] at hb
  rw [div_lt_iff₀ (by positivity)]
  push_cast
  linarith

/-- The identity permutation has no bad arcs, so it is good at every positive
level. -/
theorem isEpsilonGood_one (Y : FiniteModel) (S : Finset (Equiv.Perm Y)) {ε : ℝ}
    (hε : 0 < ε) (hY : 0 < Fintype.card Y) : IsEpsilonGood Y S ε 1 := by
  have hempty : badArcs Y S 1 = ∅ := by
    ext q
    simp [mem_badArcs]
  have hYr : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  refine ⟨?_, ?_⟩
  · rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  · rw [inv_one, hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The swap encoding of a composite has at most the four equivariance
defects of the two factors as bad arcs for the union labels. -/
theorem card_badArcs_swap_trans_le {L : Type*} [Fintype L] [DecidableEq L]
    {Y : FiniteModel}
    (actX : L → Equiv.Perm X) (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (f : FinitePartialBijection X Y) (g : FinitePartialBijection Y Z) :
    (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ))
        (f.trans g).swapPerm).card ≤
      (f.equivarianceDefect actX actY).card + (g.equivarianceDefect actY actZ).card +
        ((g.symm.equivarianceDefect actZ actY).card +
          (f.symm.equivarianceDefect actY actX).card) := by
  have h1 := card_badArcs_image_sumAction_le actX actZ (f.trans g).swapPerm
  have h2 := card_swapEquivarianceDefect_le (f.trans g) actX actZ
  have h3 := card_equivarianceDefect_trans_le actX actY actZ f g
  have h4 := card_equivarianceDefect_trans_le actZ actY actX g.symm f.symm
  rw [← FinitePartialBijection.symm_trans] at h4
  omega

/-- The same bound for the inverse, which is again the swap involution. -/
theorem card_badArcs_swap_trans_inv_le {L : Type*} [Fintype L] [DecidableEq L]
    {Y : FiniteModel}
    (actX : L → Equiv.Perm X) (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (f : FinitePartialBijection X Y) (g : FinitePartialBijection Y Z) :
    (badArcs (sumModel X Z) (Finset.univ.image (sumAction actX actZ))
        (f.trans g).swapPerm⁻¹).card ≤
      (f.equivarianceDefect actX actY).card + (g.equivarianceDefect actY actZ).card +
        ((g.symm.equivarianceDefect actZ actY).card +
          (f.symm.equivarianceDefect actY actX).card) := by
  rw [card_badArcs_inv]
  exact card_badArcs_swap_trans_le actX actY actZ f g

/-! ### The combined approximation -/

section Combined

variable {K : Type} [Group K]

/-- Approximate actions on two sequences of models, combined summandwise.
The second factor of `K × Unit` is inert. -/
noncomputable def sumApproximation (modelX modelZ : ℕ → FiniteModel)
    (actX : ∀ n, K → Equiv.Perm (modelX n)) (actZ : ∀ n, K → Equiv.Perm (modelZ n))
    (hposX : ∀ n, 0 < Fintype.card (modelX n))
    (hposZ : ∀ n, 0 < Fintype.card (modelZ n))
    (hcard : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, M ≤ Fintype.card (modelX n))
    (hmulX : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelX n) (actX n (g * h)) (actX n g * actX n h) < ε)
    (hmulZ : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelZ n) (actZ n (g * h)) (actZ n g * actZ n h) < ε) :
    MultiplicativeApproximation (K × Unit) where
  model n := sumModel (modelX n) (modelZ n)
  map n p := Equiv.sumCongr (actX n p.1) (actZ n p.1)
  card_tendsToInfinity M := by
    obtain ⟨N, hN⟩ := hcard M
    refine ⟨N, fun n hn ↦ ?_⟩
    have hsum : Fintype.card (sumModel (modelX n) (modelZ n)) =
        Fintype.card (modelX n) + Fintype.card (modelZ n) := Fintype.card_sum
    rw [hsum]
    exact (hN n hn).trans (Nat.le_add_right _ _)
  asymptoticallyMultiplicative p q ε hε := by
    obtain ⟨NX, hNX⟩ := hmulX p.1 q.1 ε hε
    obtain ⟨NZ, hNZ⟩ := hmulZ p.1 q.1 ε hε
    refine ⟨max NX NZ, fun n hn ↦ ?_⟩
    have hprod : Equiv.sumCongr (actX n p.1) (actZ n p.1) *
          Equiv.sumCongr (actX n q.1) (actZ n q.1) =
        (Equiv.sumCongr (actX n p.1 * actX n q.1) (actZ n p.1 * actZ n q.1) :
          Equiv.Perm (sumModel (modelX n) (modelZ n))) :=
      Equiv.Perm.sumCongr_mul _ _ _ _
    show hammingDistance (sumModel (modelX n) (modelZ n))
        (Equiv.sumCongr (actX n (p * q).1) (actZ n (p * q).1))
        (Equiv.sumCongr (actX n p.1) (actZ n p.1) *
          Equiv.sumCongr (actX n q.1) (actZ n q.1)) < ε
    rw [hprod, Prod.fst_mul]
    exact hammingDistance_sumCongr_lt _ _ _ _ (hposX n) (hposZ n)
      (hNX n ((le_max_left _ _).trans hn)) (hNZ n ((le_max_right _ _).trans hn))

open Classical in
/-- The labels of the combined approximation are the union labels of the
finite repair step, for the tags `↥S`. -/
theorem multiplicativeProductLabels_sumApproximation
    (modelX modelZ : ℕ → FiniteModel)
    (actX : ∀ n, K → Equiv.Perm (modelX n)) (actZ : ∀ n, K → Equiv.Perm (modelZ n))
    (hposX : ∀ n, 0 < Fintype.card (modelX n))
    (hposZ : ∀ n, 0 < Fintype.card (modelZ n))
    (hcard : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, M ≤ Fintype.card (modelX n))
    (hmulX : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelX n) (actX n (g * h)) (actX n g * actX n h) < ε)
    (hmulZ : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelZ n) (actZ n (g * h)) (actZ n g * actZ n h) < ε)
    (S : Finset K) (n : ℕ) :
    multiplicativeProductLabels
        (sumApproximation modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ) n S =
      Finset.univ.image
        (sumAction (fun t : S ↦ actX n t.1) (fun t : S ↦ actZ n t.1)) := by
  unfold multiplicativeProductLabels
  ext σ
  constructor
  · intro hσ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_univ _, rfl⟩
  · intro hσ
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hσ
    exact Finset.mem_image.mpr ⟨t.1, t.2, rfl⟩

/-- Distinct labels on the left summand stay distinct on the union. -/
theorem injOn_sumApproximation_map
    (modelX modelZ : ℕ → FiniteModel)
    (actX : ∀ n, K → Equiv.Perm (modelX n)) (actZ : ∀ n, K → Equiv.Perm (modelZ n))
    (hposX : ∀ n, 0 < Fintype.card (modelX n))
    (hposZ : ∀ n, 0 < Fintype.card (modelZ n))
    (hcard : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, M ≤ Fintype.card (modelX n))
    (hmulX : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelX n) (actX n (g * h)) (actX n g * actX n h) < ε)
    (hmulZ : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      hammingDistance (modelZ n) (actZ n (g * h)) (actZ n g * actZ n h) < ε)
    (S : Finset K) (n : ℕ) (hinj : Set.InjOn (actX n) (S : Set K)) :
    Set.InjOn
      (fun x : K ↦
        (sumApproximation modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ).map n
          (x, (1 : Unit)))
      (S : Set K) := by
  intro x hx y hy hxy
  apply hinj hx hy
  ext w
  have hw := congrArg
    (fun τ : Equiv.Perm (sumModel (modelX n) (modelZ n)) ↦ τ (Sum.inl w)) hxy
  exact Sum.inl_injective hw

end Combined

end CentralizerNormalizationSumApproximation
end GroupApproximation
