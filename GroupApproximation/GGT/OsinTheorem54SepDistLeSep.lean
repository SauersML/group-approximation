import GroupApproximation.GGT.OsinTheorem54SepDistStep

/-!
# Lemma 5.10, left half

`d_{Y⊔ℋ}(f,g) ≤ 2·sep(f,g) + 1`: a geodesic decomposes into gaps that are
letters of `Y` and crossings that are letters of `ℋ`, one crossing per
separating coset and one more gap than crossings.

The induction is on `sep(f,g)`, cutting at the FIRST penetration index globally
over all `λ`.  Three pieces, each landed:

* the prefix before the cut separates nothing (`sepSet_prefix_eq_empty`), so it
  is one `Y`-letter (`wordDist_enlargedY_le_one`);
* the crossing's span lies in `H_μ` (`span_mem_fam_of_isComp`), so it is one
  `ℋ`-letter;
* the suffix separates strictly less (`ncard_sepIndexSet_suffix_le` and
  `..._lt` through the enumeration bridge), so the inductive hypothesis applies.

Adding: `1 + 1 + (2(n-1) + 1) = 2n + 1`.

Conditional on `LemmaFourEight` at every index — `sepCard` counts an `ncard`,
and without 4.8 the set is not known to be finite, so even the base case needs
it.
-/

namespace GroupApproximation
namespace GGT
namespace OsinEnlargement

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Osin, Lemma 5.10, left half.**  This is `SepDataFam`'s `dist_le_sep` for
the canonical count. -/
theorem dist_le_sep_enlargedY [Fintype Λ] (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (h48 : ∀ lam : Λ, LemmaFourEight D lam Dc) (f g : G) :
    wordDist (enlargedY D hDc hsymm).alphabet.carrier f g
      ≤ 2 * (∑ lam : Λ, sepCard D lam Dc f g) + 1 := by
  have key : ∀ n : ℕ, ∀ f g : G, (∑ lam : Λ, sepCard D lam Dc f g) ≤ n →
      wordDist (enlargedY D hDc hsymm).alphabet.carrier f g
        ≤ 2 * (∑ lam : Λ, sepCard D lam Dc f g) + 1 := by
    intro n
    induction n with
    | zero =>
        intro f g hle
        have h0 : (∑ lam : Λ, sepCard D lam Dc f g) = 0 := by omega
        have hb := wordDist_enlargedY_le_one_of_sepCard D hDc hsymm h48 h0
        omega
    | succ n ih =>
        intro f g hle
        by_cases h0 : (∑ lam : Λ, sepCard D lam Dc f g) = 0
        · have hb := wordDist_enlargedY_le_one_of_sepCard D hDc hsymm h48 h0
          omega
        · obtain ⟨w, hw⟩ := existsGeodesicWord D f g
          -- some index separates, so some geodesic penetration exists
          have hex : ∃ m : ℕ, ∃ mu : Λ, ∃ c : G ⧸ D.fam mu,
              c ∈ sepSet D mu Dc f g ∧ PenetratesAt D mu Dc f w m c := by
            have hsome : ∃ mu : Λ, sepCard D mu Dc f g ≠ 0 := by
              by_contra hcon
              push Not at hcon
              exact h0 (Finset.sum_eq_zero (fun mu _ => hcon mu))
            obtain ⟨mu, hmu⟩ := hsome
            obtain ⟨c, hc⟩ := Set.nonempty_of_ncard_ne_zero hmu
            obtain ⟨i, k, hEP, hcc⟩ := (h48 mu).1 f g w hw c hc
            exact ⟨i, mu, c, hc, ⟨⟨k, hEP⟩, hcc⟩⟩
          obtain ⟨n₀, ⟨mu, c, hc, ⟨⟨k₀, hEP⟩, hcc⟩⟩, hmin'⟩ :=
            exists_min_penetration _ hex
          have hmin : ∀ (nu : Λ) (m : ℕ) (c' : G ⧸ D.fam nu), m < n₀ →
              c' ∈ sepSet D nu Dc f g → ¬ PenetratesAt D nu Dc f w m c' :=
            fun nu m c' hm hc' hpen => hmin' m hm ⟨nu, c', hc', hpen⟩
          -- the prefix is one `Y`-letter
          have hd1 : wordDist (enlargedY D hDc hsymm).alphabet.carrier f
              (vertex f w n₀) ≤ 1 :=
            wordDist_enlargedY_le_one D hDc hsymm
              (sepSet_prefix_eq_empty D Dc h48 hw hEP hmin)
          -- the crossing is one `ℋ`-letter
          have hd2 : wordDist (enlargedY D hDc hsymm).alphabet.carrier
              (vertex f w n₀) (vertex f w k₀) ≤ 1 := by
            show wordNorm (enlargedY D hDc hsymm).alphabet.carrier
              ((vertex f w n₀)⁻¹ * vertex f w k₀) ≤ 1
            refine wordNorm_le_one_of_mem (Set.mem_union_right _ ?_)
            exact Set.mem_iUnion.mpr
              ⟨mu, span_mem_fam_of_isComp D f hw.1 hEP⟩
          -- the suffix separates strictly less
          have hkw : k₀ ≤ w.length := hEP.2.1
          have hsuf : IsGeodesicWord D (vertex f w k₀) g
              ((w.drop k₀).take (w.length - k₀)) := by
            have h := isGeodesicWord_segment D hw hkw le_rfl
            rwa [IsGeodesicWord.vertex_length_eq hw] at h
          have hlt : (∑ nu : Λ, sepCard D nu Dc (vertex f w k₀) g)
              < ∑ nu : Λ, sepCard D nu Dc f g := by
            refine Finset.sum_lt_sum (fun nu _ => ?_) ⟨mu, Finset.mem_univ mu, ?_⟩
            · rw [sepCard_eq_ncard_sepIndexSet D nu Dc (h48 nu) hsuf,
                sepCard_eq_ncard_sepIndexSet D nu Dc (h48 nu) hw]
              exact ncard_sepIndexSet_suffix_le D Dc hw hEP
            · rw [sepCard_eq_ncard_sepIndexSet D mu Dc (h48 mu) hsuf,
                sepCard_eq_ncard_sepIndexSet D mu Dc (h48 mu) hw]
              refine ncard_sepIndexSet_suffix_lt D Dc hw hEP ?_
              rw [← hcc]
              exact hc
          have hd3 := ih (vertex f w k₀) g (by omega)
          have htri := wordDist_triangle
            (enlargedY D hDc hsymm).alphabet.symmetricGenerating f
            (vertex f w n₀) g
          have htri2 := wordDist_triangle
            (enlargedY D hDc hsymm).alphabet.symmetricGenerating
            (vertex f w n₀) (vertex f w k₀) g
          omega
  exact key _ f g le_rfl

end OsinEnlargement
end GGT
end GroupApproximation
