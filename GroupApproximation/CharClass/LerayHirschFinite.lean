import GroupApproximation.CharClass.LerayHirschCover

/-!
# Leray–Hirsch over a finite cover

The two-set step is iterated here.  The induction is not on the list of open sets
directly but on its LENGTH, because the step needs the induction hypothesis for a
*different* list of the same length: to know the theorem over
`B ⊓ (U₁ ⊔ ⋯ ⊔ U_k)` one distributes and applies it to `B ⊓ U₁, …, B ⊓ U_k`.

That is why the hypothesis is phrased through a predicate `Good` closed under
intersection with an arbitrary open set, rather than through a fixed list.  For a
bundle, `Good A` is "the bundle is trivial over `A` and Leray–Hirsch holds there",
and both halves survive intersecting with anything.

## Main declarations

* `inf_foldr_sup` — distributivity, in the shape the induction consumes.
* `LHOver_foldr` — the induction over the length.
* `bijective_lhSum_of_finite_cover` — **Leray–Hirsch over a finite cover**.
* `lerayHirschGraded_of_finite_cover` — the same, in the published interface.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace

noncomputable section

variable {X P : TopCat.{0}}

/-! ## 1. Distributivity -/

/-- Intersecting a finite union distributes, in the shape the induction uses. -/
theorem inf_foldr_sup (B : Opens X) (L : List (Opens X)) (A : Opens X) :
    B ⊓ L.foldr (· ⊔ ·) A = (L.map (B ⊓ ·)).foldr (· ⊔ ·) (B ⊓ A) := by
  induction L with
  | nil => rfl
  | cons C L' ih =>
    show B ⊓ (C ⊔ L'.foldr (· ⊔ ·) A)
      = (B ⊓ C) ⊔ (L'.map (B ⊓ ·)).foldr (· ⊔ ·) (B ⊓ A)
    rw [inf_sup_left, ih]

/-! ## 2. The induction -/

/-- **Leray–Hirsch over a finite union of good open sets.**  The induction is on the
length, because the step applies the hypothesis to a different list of the same
length. -/
theorem LHOver_foldr (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ) (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A) :
    ∀ (k : ℕ) (L : List (Opens X)), L.length ≤ k → (∀ B ∈ L, Good B) →
      ∀ A : Opens X, Good A → LHOver f ξ r (L.foldr (· ⊔ ·) A) := by
  intro k
  induction k with
  | zero =>
    intro L hL _ A hA
    cases L with
    | nil => exact hLH A hA
    | cons B L' => exact absurd hL (by simp)
  | succ k ih =>
    intro L hL hGood A hA
    cases L with
    | nil => exact hLH A hA
    | cons B L' =>
      have hB : Good B := hGood B (by simp)
      have hGood' : ∀ C ∈ L', Good C := fun C hC => hGood C (by simp [hC])
      have hL' : L'.length ≤ k := by
        have h := hL
        simp only [List.length_cons] at h
        omega
      have h1 : LHOver f ξ r (L'.foldr (· ⊔ ·) A) := ih L' hL' hGood' A hA
      have h2 : LHOver f ξ r (B ⊓ L'.foldr (· ⊔ ·) A) := by
        rw [inf_foldr_sup]
        refine ih (L'.map (B ⊓ ·)) (by simpa using hL') ?_ (B ⊓ A) (hinf B A hB)
        intro C hC
        obtain ⟨D, _, rfl⟩ := List.mem_map.mp hC
        exact hinf B D hB
      show LHOver f ξ r (B ⊔ L'.foldr (· ⊔ ·) A)
      exact LHOver_sup f ξ r B (L'.foldr (· ⊔ ·) A) (hLH B hB) h1 h2

/-! ## 3. Leray–Hirsch over a finite cover -/

/-- **Leray–Hirsch over a finite cover.**  If the powers of `ξ` are a basis over every
member of a finite family of open sets that is closed under intersection with
anything, and that family covers, they are a basis over the whole total space. -/
theorem bijective_lhSum_of_finite_cover (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A)
    (L : List (Opens X)) (hGood : ∀ B ∈ L, Good B)
    (A : Opens X) (hA : Good A) (hcover : L.foldr (· ⊔ ·) A = ⊤) (n : ℕ) :
    Function.Bijective (lhSum f ξ r n) := by
  refine LHOver_top f ξ r ?_ n
  rw [← hcover]
  exact LHOver_foldr f ξ r Good hinf hLH L.length L le_rfl hGood A hA

/-- **The same, in the published interface.** -/
theorem lerayHirschGraded_of_finite_cover (f : P ⟶ X) (ξ : Hmod2 P 2) (r : ℕ)
    (Good : Opens X → Prop)
    (hinf : ∀ A W : Opens X, Good A → Good (A ⊓ W))
    (hLH : ∀ A : Opens X, Good A → LHOver f ξ r A)
    (L : List (Opens X)) (hGood : ∀ B ∈ L, Good B)
    (A : Opens X) (hA : Good A) (hcover : L.foldr (· ⊔ ·) A = ⊤) :
    LerayHirschGraded f ξ r :=
  lerayHirschGraded_of_bijective f ξ r fun n =>
    bijective_lhSum_of_finite_cover f ξ r Good hinf hLH L hGood A hA hcover n

end

end LH
end CharClass
end GroupApproximation
