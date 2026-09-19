import GroupApproximation.GGT.OsinTheorem54SepLetterCount
import GroupApproximation.GGT.OsinTheorem54SepInhabit

/-!
# One letter separates at most one coset, summed over `Λ`

`GGT/OsinTheorem54SepLetterCount.lean` proves the per-`λ` bound: a single letter
separates at most one coset of `H_λ`.  Lemma 5.10's right half needs it for the
`Λ`-SUM, and there it is **not** automatic — a letter lying in `H_λ` and `H_μ`
and deep for both contributes the two distinct cosets `1·H_λ` and `1·H_μ`.

So the summed bound carries a hypothesis on the family:

  no element is deep for two indices at once.

`hmult` below states it in the relative-ball vocabulary.  Its provenance, which
makes it a choice of `Dc` rather than a new leaf: for a hyperbolically embedded
family the pairwise intersections `H_λ ∩ H_μ` are FINITE — Dahmani--Guirardel--
Osin's Proposition 4.35, which is NOT in this repository and is named here as
the fact `hmult` reduces to — so with `Λ` finite and `Dc` chosen above the
`d̂`-radius of every pairwise intersection, no element of an intersection is
deep for either index and `hmult` holds.

`deep_of_sepCard_ne_zero` is what makes the reduction go: a letter that
separates anything at `λ` is a `λ`-letter AND deep for `λ`, so two indices with
a nonzero count would be two indices the letter is deep for.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A letter that separates is a letter of that subgroup, and deep in it.**

The geodesic from `1` to a letter has length at most one, so a component of it
is the whole word, its span is the letter itself, and essentiality says exactly
that the letter escapes the ball. -/
theorem deep_of_sepCard_ne_zero (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    (_h48 : LemmaFourEight D lam Dc) {h : G}
    (hmem : h ∈ D.alphabet.carrier) (hne : sepCard D lam Dc 1 h ≠ 0) :
    h ∈ D.fam lam ∧ h ∉ D.relBall lam Dc := by
  obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨w, i, k, hgw, hEP, -⟩ := hc
  obtain ⟨hik, hkw, hrange, -, -⟩ := hEP.1
  -- the geodesic to a letter has length one
  have hlen1 : w.length ≤ 1 := by
    rw [hgw.2.2, wordDist_one_left]
    exact wordNorm_le_one_of_mem hmem
  have hi0 : i = 0 := by omega
  have hk1 : k = 1 := by omega
  have hwlen : w.length = 1 := by omega
  subst hi0
  subst hk1
  have h0w : (0 : ℕ) < w.length := by omega
  -- its single letter spells `h`
  have hval : (w[0]'h0w).val = h := by
    have hv := vertex_succ w (1 : G) 0 h0w
    rw [vertex_zero, one_mul] at hv
    have hend : vertex (1 : G) w w.length = h := IsGeodesicWord.vertex_length_eq hgw
    rw [hwlen] at hend
    rw [← hv]
    exact hend
  refine ⟨?_, ?_⟩
  · have hcl := hrange 0 le_rfl hik h0w
    have := val_mem_fam_of_isCompOf D (hgw.1 _ (List.getElem_mem h0w)) hcl
    rwa [hval] at this
  · have hspan := hEP.2
    rw [vertex_zero, inv_one, one_mul] at hspan
    have hend : vertex (1 : G) w 1 = h := by
      have hv := vertex_succ w (1 : G) 0 h0w
      rw [vertex_zero, one_mul, hval] at hv
      exact hv
    rwa [hend] at hspan

/-- **The summed per-letter bound**, under the multiplicity hypothesis. -/
theorem sepCard_sum_le_one_of_mem_alphabet [Fintype Λ] (D : RelGenSet G Λ)
    (Dc : ℕ) (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc)
    (hmult : ∀ lam mu : Λ, lam ≠ mu → ∀ x : G, x ∈ D.fam lam → x ∈ D.fam mu →
      x ∈ D.relBall lam Dc ∨ x ∈ D.relBall mu Dc)
    {h : G} (hmem : h ∈ D.alphabet.carrier) :
    (∑ lam : Λ, sepCard D lam Dc 1 h) ≤ 1 := by
  classical
  by_cases hall : ∀ lam : Λ, sepCard D lam Dc 1 h = 0
  · rw [Finset.sum_eq_zero (fun lam _ => hall lam)]
    omega
  · push Not at hall
    obtain ⟨nu, hnu⟩ := hall
    -- every other index contributes nothing, by the multiplicity hypothesis
    have hzero : ∀ lam : Λ, lam ≠ nu → sepCard D lam Dc 1 h = 0 := by
      intro lam hne
      by_contra hlam
      obtain ⟨hfl, hdl⟩ := deep_of_sepCard_ne_zero D lam Dc (h48 lam) hmem hlam
      obtain ⟨hfn, hdn⟩ := deep_of_sepCard_ne_zero D nu Dc (h48 nu) hmem hnu
      rcases hmult lam nu hne h hfl hfn with hb | hb
      · exact hdl hb
      · exact hdn hb
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ nu),
      Finset.sum_eq_zero (fun lam hlam =>
        hzero lam (Finset.ne_of_mem_erase hlam)), add_zero]
    exact sepCard_le_one_of_mem_alphabet (h48 nu) hmem

end OsinComponents
end GGT
end GroupApproximation
