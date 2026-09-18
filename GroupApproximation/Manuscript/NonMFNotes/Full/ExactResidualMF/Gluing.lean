import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Sofic.WeakMFNonsoficDouble

/-!
# Gluing two unitary families into the symmetric double

Source: `non_mf_group_notes.tex`, proof of `thm:exact-mf-residual`, and
Shulman (arXiv:2603.13564), Theorem 10: a faithful corona representation of
the symmetric double `G *_Γ G` is produced from two matrix families
`Φ true`, `Φ false : G →* ∏ₙ U(Xₙ)` which agree on `Γ` modulo operator-norm
null sequences and which separate every word of letters that is nontrivial
in the double.

This file proves that gluing criterion from the universal property of
`PushoutI`, together with the elementary word calculus and the non-null test
used later.
-/

namespace GroupApproximation.Full.NN01b

open GroupApproximation Monoid

section Words

variable (G : Type) [Group G]

/-- Evaluate a word of letters `(copy, element)` with a family of maps. -/
def wordEval {K : Type*} [Monoid K] (f : Bool → G → K) (l : List (Bool × G)) : K :=
  (l.map fun p => f p.1 p.2).prod

theorem wordEval_nil {K : Type*} [Monoid K] (f : Bool → G → K) :
    wordEval G f [] = 1 := rfl

theorem wordEval_cons {K : Type*} [Monoid K] (f : Bool → G → K) (p : Bool × G)
    (l : List (Bool × G)) :
    wordEval G f (p :: l) = f p.1 p.2 * wordEval G f l := rfl

theorem wordEval_singleton {K : Type*} [Monoid K] (f : Bool → G → K) (p : Bool × G) :
    wordEval G f [p] = f p.1 p.2 := by
  rw [wordEval_cons, wordEval_nil, mul_one]

theorem wordEval_append {K : Type*} [Monoid K] (f : Bool → G → K)
    (l₁ l₂ : List (Bool × G)) :
    wordEval G f (l₁ ++ l₂) = wordEval G f l₁ * wordEval G f l₂ := by
  induction l₁ with
  | nil => exact (one_mul _).symm
  | cons p l ih => rw [List.cons_append, wordEval_cons, wordEval_cons, ih, mul_assoc]

theorem map_wordEval {K L : Type*} [Monoid K] [Monoid L] (F : K →* L)
    (f : Bool → G → K) (l : List (Bool × G)) :
    F (wordEval G f l) = wordEval G (fun b g => F (f b g)) l := by
  induction l with
  | nil => exact map_one F
  | cons p l ih => rw [wordEval_cons, wordEval_cons, map_mul, ih]

end Words

section Double

variable (G : Type) [Group G] (Γ : Subgroup G)

/-- Every element of the symmetric double is a word in the two copies of `G`. -/
theorem exists_word (x : SymmetricDouble G Γ) :
    ∃ l : List (Bool × G), wordEval G (fun b g => inDouble G Γ b g) l = x := by
  induction x using PushoutI.induction_on with
  | of b g => exact ⟨[(b, g)], wordEval_singleton G (fun b g => inDouble G Γ b g) (b, g)⟩
  | base h =>
    exact ⟨[(true, (h : G))],
      (wordEval_singleton G (fun b g => inDouble G Γ b g) (true, (h : G))).trans
        (PushoutI.of_apply_eq_base (doubleMap G Γ) true h)⟩
  | mul x y hx hy =>
    obtain ⟨lx, rfl⟩ := hx
    obtain ⟨ly, rfl⟩ := hy
    exact ⟨lx ++ ly, wordEval_append G _ lx ly⟩

/-- The two copies of `G` agree on `Γ` inside the double. -/
theorem inDouble_agree (c : Γ) (b b' : Bool) :
    inDouble G Γ b (c : G) = inDouble G Γ b' (c : G) :=
  (PushoutI.of_apply_eq_base (doubleMap G Γ) b c).trans
    (PushoutI.of_apply_eq_base (doubleMap G Γ) b' c).symm

end Double

section Corona

/-- A unitary sequence whose operator distance to the identity is eventually at
least one is not null. -/
theorem not_mem_nullCofiniteOpSubgroup_of_eventually {X : ℕ → FiniteModel}
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) (N : ℕ)
    (h : ∀ n, N ≤ n → 1 ≤ opLength (X n) (v n)) :
    v ∉ nullCofiniteOpSubgroup X := by
  intro hv
  have hv' : ∀ᶠ n in Filter.cofinite, opLength (X n) (v n) < 1 := hv 1 one_pos
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hv'
  obtain ⟨a, ha⟩ := hv'
  exact absurd (ha (max a N) (le_max_left a N)) (not_lt.mpr (h (max a N) (le_max_right a N)))

variable (G : Type) [Group G] (Γ : Subgroup G)

/-- **Gluing criterion.**  Two unitary families of `G` that agree on `Γ` modulo
null sequences and separate the nontrivial words of the double give an
operator-norm MF embedding of `G *_Γ G` (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`; Shulman, Theorem 10). -/
theorem isOperatorMF_symmetricDouble_of_gluing (X : ℕ → FiniteModel)
    (hX : ∀ n, 0 < Fintype.card (X n))
    (Φ : Bool → G →* (∀ n, Matrix.unitaryGroup (X n) ℂ))
    (hagree : ∀ c : Γ, (Φ true (c : G))⁻¹ * Φ false (c : G) ∈ nullCofiniteOpSubgroup X)
    (hsep : ∀ l : List (Bool × G),
      wordEval G (fun b g => Φ b g) l ∈ nullCofiniteOpSubgroup X →
        wordEval G (fun b g => inDouble G Γ b g) l = 1) :
    IsOperatorMF (SymmetricDouble G Γ) := by
  have hf : ∀ b : Bool,
      ((QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (Φ b)).comp (doubleMap G Γ b) =
        ((QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (Φ true)).comp Γ.subtype := by
    intro b
    cases b with
    | false => exact MonoidHom.ext fun c => (QuotientGroup.eq.mpr (hagree c)).symm
    | true => rfl
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SymmetricDouble G Γ →* NormMatrixCoronaUnitary X,
      ∀ b g, ρ (inDouble G Γ b g) = QuotientGroup.mk' (nullCofiniteOpSubgroup X) (Φ b g) :=
    ⟨PushoutI.lift (fun b => (QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (Φ b))
      (((QuotientGroup.mk' (nullCofiniteOpSubgroup X)).comp (Φ true)).comp Γ.subtype) hf,
      fun b g => PushoutI.lift_of _ _ hf (i := b) g⟩
  refine ⟨X, hX, ρ, (injective_iff_map_eq_one ρ).mpr ?_⟩
  intro x hx
  obtain ⟨l, rfl⟩ := exists_word G Γ x
  apply hsep l
  have hq : QuotientGroup.mk' (nullCofiniteOpSubgroup X) (wordEval G (fun b g => Φ b g) l) = 1 :=
    calc QuotientGroup.mk' (nullCofiniteOpSubgroup X) (wordEval G (fun b g => Φ b g) l)
        = wordEval G (fun b g => QuotientGroup.mk' (nullCofiniteOpSubgroup X) (Φ b g)) l :=
          map_wordEval G _ _ l
      _ = wordEval G (fun b g => ρ (inDouble G Γ b g)) l := by simp only [hρ]
      _ = ρ (wordEval G (fun b g => inDouble G Γ b g) l) := (map_wordEval G ρ _ l).symm
      _ = 1 := hx
  exact (QuotientGroup.eq_one_iff (N := nullCofiniteOpSubgroup X)
    (wordEval G (fun b g => Φ b g) l)).mp hq

end Corona

end GroupApproximation.Full.NN01b
