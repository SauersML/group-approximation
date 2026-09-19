import GroupApproximation.GGT.OsinTheorem54SepLetterMult

/-!
# Lemma 5.10, right half

`sep(f,g) ≤ 3·d_{Y⊔ℋ}(f,g)`, where `sep` is the Λ-sum `∑ λ, |S(f,g;D)_λ|` and
the distance is taken in the ENLARGED alphabet.

The induction is on a geodesic word of that alphabet, one letter at a time.
Two facts are used, and both are landed:

* the defect-two triangle inequality `h49` for the sum, with the midpoint taken
  one letter along the word;
* the per-letter bound: one letter of `Y ⊔ ℋ` separates at most one coset in
  total.

The constant is `3 = 1 + 2`: one for the letter, two for the defect.  Nothing
here looks at the geometry --- the letters are opaque, and a coarser per-letter
bound `c` would simply give `c + 2` in place of `3`.

## Where the per-letter bound comes from

For a letter of `ℋ` it is `sepCard_sum_le_one_of_mem_alphabet`, and that is the
only place `hmult` is spent; `GGT/OsinTheorem54SepLetterMult.lean` records what
the hypothesis says and what it reduces to.

For a letter of `Y` the count is not merely small but ZERO, and by definition
rather than by an argument: `y ∈ Y` says exactly that `S(1,y;D)_λ = ∅` at every
`λ`.  So the enlargement's own letters are free, and the whole cost of an
enlarged geodesic is carried by its `ℋ`-letters.  This is the asymmetry that
makes Osin's two halves of Lemma 5.10 different in character: the left half has
to produce the `Y`-letters, the right half only has to know they cost nothing.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **One letter of the enlarged alphabet separates at most one coset.**

The two cases are genuinely different: a letter of `ℋ` is a letter of the
original alphabet and is counted by `sepCard_sum_le_one_of_mem_alphabet`, while
a letter of `Y` separates nothing at all. -/
theorem sepCard_sum_le_one_of_mem_enlarged [Fintype Λ] (D : RelGenSet G Λ)
    {Dc : ℕ} (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hmult : ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc)
    {b : G} (hb : b ∈ (enlargedY D hDc hsymm).alphabet.carrier) :
    (∑ lam : Λ, sepCard D lam Dc 1 b) ≤ 1 := by
  have hb' : b ∈ {y : G | ∀ lam : Λ, sepSet D lam Dc 1 y = ∅} ∪
      (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := hb
  rcases hb' with hy | hy
  · have hyy : ∀ lam : Λ, sepSet D lam Dc 1 b = ∅ := hy
    have hzero : ∀ lam : Λ, sepCard D lam Dc 1 b = 0 := by
      intro lam
      show (sepSet D lam Dc 1 b).ncard = 0
      rw [hyy lam, Set.ncard_empty]
    rw [Finset.sum_eq_zero (fun lam _ => hzero lam)]
    omega
  · have hmem : b ∈ D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) :=
      Or.inr hy
    exact sepCard_sum_le_one_of_mem_alphabet D Dc h48 hmult hmem

/-- **The word induction.**  Along a word of the enlarged alphabet the count
grows by at most three per letter: one for the letter, two for the defect of
`h49`.  The word is not assumed geodesic --- geodesy enters only at the last
step, to identify its length with the distance. -/
theorem sepCard_sum_le_of_isWord [Fintype Λ] (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hmult : ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc)
    (h49 : ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2) :
    ∀ l : List G, (∀ x ∈ l, x ∈ (enlargedY D hDc hsymm).alphabet.carrier) →
      ∀ f : G, (∑ lam : Λ, sepCard D lam Dc f (f * l.prod)) ≤ 3 * l.length := by
  intro l
  induction l with
  | nil =>
      intro _ f
      rw [List.prod_nil, mul_one, List.length_nil, mul_zero]
      exact le_of_eq (Finset.sum_eq_zero (fun lam _ => sepCard_self D lam Dc f))
  | cons a t ih =>
      intro hl f
      have ha : a ∈ (enlargedY D hDc hsymm).alphabet.carrier :=
        hl a List.mem_cons_self
      have ht : ∀ x ∈ t, x ∈ (enlargedY D hDc hsymm).alphabet.carrier :=
        fun x hx => hl x (List.mem_cons_of_mem a hx)
      have hprod : f * (a :: t).prod = f * a * t.prod := by
        rw [List.prod_cons, mul_assoc]
      rw [hprod, List.length_cons]
      have htri := h49 f (f * a * t.prod) (f * a)
      have hstep : (∑ lam : Λ, sepCard D lam Dc (f * a * t.prod) (f * a))
          ≤ 3 * t.length := by
        have hEq : (∑ lam : Λ, sepCard D lam Dc (f * a * t.prod) (f * a))
            = ∑ lam : Λ, sepCard D lam Dc (f * a) (f * a * t.prod) :=
          Finset.sum_congr rfl
            (fun lam _ => sepCard_comm D lam Dc hsymm (f * a * t.prod) (f * a))
        rw [hEq]
        exact ih ht (f * a)
      have hletter : (∑ lam : Λ, sepCard D lam Dc f (f * a)) ≤ 1 := by
        have hEq : (∑ lam : Λ, sepCard D lam Dc f (f * a))
            = ∑ lam : Λ, sepCard D lam Dc 1 a := by
          refine Finset.sum_congr rfl (fun lam _ => ?_)
          have h1 := sepCard_smul D lam Dc f 1 a
          rwa [mul_one] at h1
        rw [hEq]
        exact sepCard_sum_le_one_of_mem_enlarged D hDc hsymm h48 hmult ha
      omega

/-- **Osin, Lemma 5.10, right half.**  This is `SepDataFam`'s `sep_le_dist` for
the canonical count, and the last of the two halves. -/
theorem sep_le_dist_enlargedY [Fintype Λ] (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hmult : ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc)
    (h49 : ∀ f g h : G, (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ (∑ lam : Λ, sepCard D lam Dc f h)
        + (∑ lam : Λ, sepCard D lam Dc g h) + 2) (f g : G) :
    (∑ lam : Λ, sepCard D lam Dc f g)
      ≤ 3 * wordDist (enlargedY D hDc hsymm).alphabet.carrier f g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq
    (enlargedY D hDc hsymm).alphabet.symmetricGenerating (f⁻¹ * g)
  have hg : f * l.prod = g := by
    rw [hl.prod_eq, mul_inv_cancel_left]
  have hkey := sepCard_sum_le_of_isWord D hDc hsymm h48 hmult h49 l hl.letters f
  rw [hg] at hkey
  have hdist : wordDist (enlargedY D hDc hsymm).alphabet.carrier f g
      = l.length := by
    unfold wordDist
    rw [hlen]
  rw [hdist]
  exact hkey

end OsinEnlargement
end GGT
end GroupApproximation
