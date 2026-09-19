import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# One letter separates at most one coset

The per-letter half of Osin's Lemma 5.10, right-hand inequality.

`sep_le_dist` asks for `|S(f,g;D)| ≤ 3 d_{Y⊔ℋ}(f,g)`, and the constant `3` is
not chosen --- it falls out of the two inputs.  Along a geodesic of the enlarged
Cayley graph, iterating the defect-two triangle inequality over `n` steps gives

  `sep(x₀,xₙ) ≤ Σᵢ sep(xᵢ,xᵢ₊₁) + 2(n-1)`,

and each single step contributes at most one **per `λ`**, so the total is at
most `n + 2(n-1) = 3n - 2` **provided no single letter is deep for two indices
at once**.

That proviso is not vacuous and I first stated this without it.  `sep` is the
`Λ`-SUM, and a letter lying in `H_λ` and `H_μ` for `λ ≠ μ` and deep for both
contributes the two DISTINCT cosets `1·H_λ` and `1·H_μ`, so that step
contributes two rather than one.  In general a step contributes at most
`m := #{λ | the letter is in H_λ and deep for λ}`, and the iteration gives
`(m+2)·n − 2`; the field's constant `3` is the case `m ≤ 1`.

Both lemmas below are per `λ` and are unaffected.  What needs the proviso is the
summed version, which is why `hmult` appears as a hypothesis where the sum is
taken.  Its provenance: for a hyperbolically embedded family the pairwise
intersections `H_λ ∩ H_μ` are finite --- Dahmani--Guirardel--Osin's
Proposition 4.35, which is NOT in this repository and is named here as the fact
`hmult` reduces to --- so with `Λ` finite and `Dc` chosen above the `d̂`-radius
of every pairwise intersection, no element is deep for two indices and `hmult`
is discharged by a choice of `Dc` rather than by a new leaf.

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
