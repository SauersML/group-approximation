import GroupApproximation.GGT.DGOWWordConditions
import GroupApproximation.GGT.OsinPenetration

/-!
# Gerasimova–Osin's words `t f₁ t f₂ ⋯ t fₙ`

Gerasimova–Osin (arXiv:1910.14524v3), §4, after (16):

> Let `w` be a word in the alphabet `𝒜` of the form `w = t f₁ t f₂ … t fₙ`, where
> `f₁, …, fₙ` are some letters from `F` (note that we use the assumption (15) here).

Here `H = ⟨y⟩ ↪h (G, X)`, `F ⊆ X` and `t ∈ H` with `d̂(1,t) > 5C`, so `t` is read as a
letter of `H` and each `fᵢ` as a letter of `X`.  `altWord t fs` is that word over the
relative alphabet `X ⊔ H` of the repository (`GGT.RelLetter G Unit`), the canonical
decomposition `p = a₁b₁ ⋯ aₙbₙ` of (17)–(18) being the even and odd positions.

The three conditions `(W1)`–`(W3)` of Dahmani–Guirardel–Osin's Lemma 4.21
(`GGT.WWord`) hold for these words, from `F ∩ H = ∅` (Gerasimova–Osin's Lemma 4.2) and
`t ∉ d̂`-ball: letters alternate, the only subgroup letter is `t`, and the letter
between two `t`'s is some `fᵢ ∉ H`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Gerasimova–Osin's Proposition 4.1).
Certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace GerasimovaOsinWords

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents

universe u

variable {G : Type u} [Group G]

/-- Gerasimova–Osin's word `t f₁ t f₂ ⋯ t fₙ` over `X ⊔ H`. -/
def altWord (t : G) : List G → List (RelLetter G Unit)
  | [] => []
  | f :: fs => RelLetter.comp () t :: RelLetter.base f :: altWord t fs

@[simp] theorem altWord_nil (t : G) : altWord t [] = [] := rfl

@[simp] theorem altWord_cons (t f : G) (fs : List G) :
    altWord t (f :: fs) = RelLetter.comp () t :: RelLetter.base f :: altWord t fs := rfl

theorem length_altWord (t : G) (fs : List G) : (altWord t fs).length = 2 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [altWord_cons, List.length_cons, ih]
    ring

/-- The element spelled by `t f₁ ⋯ t fₙ` is `(t f₁) ⋯ (t fₙ)`. -/
theorem listVal_altWord (t : G) (fs : List G) :
    RelLetter.listVal (altWord t fs) = (fs.map fun f => t * f).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [altWord_cons, listVal_cons, listVal_cons, ih, List.map_cons, List.prod_cons,
      ← mul_assoc]
    rfl

theorem getElem?_altWord_even (t : G) (fs : List G) (i : ℕ) :
    (altWord t fs)[2 * i]? = fs[i]?.map fun _ => RelLetter.comp () t := by
  induction fs generalizing i with
  | nil => simp
  | cons f fs ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, altWord_cons, List.getElem?_cons_succ,
        List.getElem?_cons_succ, ih, List.getElem?_cons_succ]

theorem getElem?_altWord_odd (t : G) (fs : List G) (i : ℕ) :
    (altWord t fs)[2 * i + 1]? = fs[i]?.map RelLetter.base := by
  induction fs generalizing i with
  | nil => simp
  | cons f fs ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by ring, altWord_cons,
        List.getElem?_cons_succ, List.getElem?_cons_succ, ih, List.getElem?_cons_succ]

theorem getElem?_altWord (t : G) (fs : List G) (i : ℕ) :
    (altWord t fs)[i]? = if i % 2 = 0 then fs[i / 2]?.map (fun _ => RelLetter.comp () t)
      else fs[i / 2]?.map RelLetter.base := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
  · have h1 : 2 * k % 2 = 0 := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [getElem?_altWord_even, if_pos h1, h2]
  · have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [getElem?_altWord_odd, if_neg h1, h2]

theorem isLetter_altWord (D : RelGenSet G Unit) {t : G} (ht : t ∈ D.fam ())
    {fs : List G} (hfs : ∀ f ∈ fs, f ∈ D.base) : ∀ a ∈ altWord t fs, D.IsLetter a := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    intro a ha
    simp only [altWord_cons, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact ht
    · exact hfs f List.mem_cons_self
    · exact ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) a ha

/-- **(W1)**: the letters alternate. -/
theorem isWOne_altWord (t : G) (fs : List G) : WWord.IsWOne (altWord t fs) := by
  intro i x y hx hy
  rw [getElem?_altWord] at hx hy
  by_cases hi : i % 2 = 0
  · rw [if_pos hi] at hx
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hx
    cases e
  · rw [if_pos (by omega)] at hy
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hy
    cases e

/-- **(W2)**: the only subgroup letter is `t`. -/
theorem isWTwo_altWord (D : RelGenSet G Unit) {R : ℕ} {t : G} (ht : t ∉ D.relBall () R)
    (fs : List G) : WWord.IsWTwo D R (altWord t fs) := by
  intro i lam h hx
  rw [getElem?_altWord] at hx
  by_cases hi : i % 2 = 0
  · rw [if_pos hi] at hx
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hx
    cases e
    exact ht
  · rw [if_neg hi] at hx
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hx
    cases e

/-- **(W3)**: between two `t`'s sits some `fᵢ ∉ H`. -/
theorem isWThree_altWord (D : RelGenSet G Unit) (t : G) {fs : List G}
    (hfs : ∀ f ∈ fs, f ∉ D.fam ()) : WWord.IsWThree D (altWord t fs) := by
  refine ⟨?_, ?_⟩
  · intro i lam mu h₁ h₂ hx hy
    rw [getElem?_altWord] at hx hy
    by_cases hi : i % 2 = 0
    · rw [if_neg (by omega)] at hy
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hy
      cases e
    · rw [if_neg hi] at hx
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hx
      cases e
  · intro i lam mu h₁ h₂ x _ hy _
    right
    rw [getElem?_altWord] at hy
    by_cases hi : (i + 1) % 2 = 0
    · rw [if_pos hi] at hy
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp hy
      cases e
    · rw [if_neg hi] at hy
      obtain ⟨f, hf, e⟩ := Option.map_eq_some_iff.mp hy
      cases e
      cases lam
      exact hfs f (List.mem_of_getElem? hf)

end GerasimovaOsinWords
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.GerasimovaOsinWords

#audit_axioms listVal_altWord
#audit_axioms isWOne_altWord
#audit_axioms isWTwo_altWord
#audit_axioms isWThree_altWord
