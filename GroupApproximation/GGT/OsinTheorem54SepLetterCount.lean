import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# One letter separates at most one coset

The per-letter half of Osin's Lemma 5.10, right-hand inequality.

`sep_le_dist` asks for `|S(f,g;D)| ≤ 3 d_{Y⊔ℋ}(f,g)`, and the constant `3` is
not chosen --- it falls out of the two inputs.  Along a geodesic of the enlarged
Cayley graph, iterating the defect-two triangle inequality over `n` steps gives

  `sep(x₀,xₙ) ≤ Σᵢ sep(xᵢ,xᵢ₊₁) + 2(n-1)`,

and each single step contributes at most one, so the total is at most
`n + 2(n-1) = 3n - 2`.  That is where the `3` comes from, and it confirms the
field's constant rather than assuming it.

This module supplies the per-step half, which needs nothing but Lemma 4.8: a
letter is at word distance at most one from the identity, and a geodesic of
length at most one carries at most one component.  The other half is
`sep_triangle`, Osin's Lemma 4.9, which waits on the isolated-component bound.
So `sep_le_dist` is not an independent obligation --- it is `sep_triangle` plus
this.

Conditional on `OsinComponents.LemmaFourEight`, carried as a leading binder, as
everywhere `sepCard` is used: the count is `Set.ncard`, and without 4.8 the set
is not known to be finite.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A single letter separates at most one coset.**

A letter of `X ⊔ ℋ` is at word distance at most one from the identity, and
`sepCard_le_wordDist` bounds the count by that distance. -/
theorem sepCard_le_one_of_mem_alphabet {D : RelGenSet G Λ} {lam : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) {x : G} (hx : x ∈ D.alphabet.carrier) :
    sepCard D lam Dc 1 x ≤ 1 := by
  refine le_trans (sepCard_le_wordDist h48 1 x) ?_
  rw [wordDist_one_left]
  exact wordNorm_le_one_of_mem hx

/-- **A single peripheral element separates at most one coset**, the case the
enlarged geodesic's `ℋ`-steps present. -/
theorem sepCard_le_one_of_mem_fam {D : RelGenSet G Λ} {lam mu : Λ} {Dc : ℕ}
    (h48 : LemmaFourEight D lam Dc) {x : G} (hx : x ∈ D.fam mu) :
    sepCard D lam Dc 1 x ≤ 1 :=
  sepCard_le_one_of_mem_alphabet h48 (RelGenSet.fam_subset_alphabet D mu hx)

end OsinComponents
end GGT
end GroupApproximation
