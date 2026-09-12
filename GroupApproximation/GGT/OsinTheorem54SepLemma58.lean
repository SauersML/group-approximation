import GroupApproximation.GGT.DGOPolygonSideCountAll
import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.OsinTheorem54SepClosingEdge
import GroupApproximation.GGT.OsinTheorem54SepNontrivialWord
import GroupApproximation.GGT.OsinTheorem54SepSurgery

/-!
# Osin's Lemma 5.8: local finiteness after enlarging the base

The preceding modules contain every geometric ingredient of Osin's Lemma 5.8:

* `exists_nontrivial_word_of_mem_relBall` chooses an admissible word without
  trivial letters;
* `exists_pieces_of_enlargedWord` replaces its enlarged-base letters by
  geodesic pieces over `Z`;
* `isIsolated_closing_of_avoidsFrom` says that closing this path by the inverse
  peripheral edge gives an isolated component; and
* `isolatedComponentBound_nGon_of_fourPointHyperbolic` bounds that component at
  the one side count fixed by the radius of the ball under consideration.

This module composes those facts.  An element of the radius-`n` relative ball
for `Y` lies in one fixed relative ball for `Z`; local finiteness for `Z` was
already proved from local finiteness for the original relative generating set.
Thus the local-finiteness clause of Lemma 5.8 is no longer an input to the
assembly of Osin's Theorem 5.4.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric
open GroupApproximation.GGT.OsinEnlargement

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- The auxiliary base `Z` is symmetric when the original base is symmetric. -/
theorem relGenSetZ_base_inv_mem (D : RelGenSet G Λ) {Dc : ℕ}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    ∀ x ∈ (relGenSetZ D Dc).base, x⁻¹ ∈ (relGenSetZ D Dc).base := by
  intro x hx
  rcases hx with hx | ⟨lam, hx⟩
  · exact Or.inl (hsymm x hx)
  · exact Or.inr ⟨lam, relBall_inv D lam hsymm hx⟩

/-- **The radius-`n` relative ball for `Y` is contained in one relative ball
for `Z`.**  The displayed radius is the arbitrary-side polygon bound evaluated
at `n + 1`: at most `n` geodesic pieces come from the admissible word and one
more side closes the loop. -/
theorem relBall_enlargedY_subset_relGenSetZ (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ)
    (lam : Λ) (n : ℕ) :
    (enlargedY D hDc hsymm).relBall lam n ⊆
      (relGenSetZ D Dc).relBall lam
        (((n + 1) + 1) * (25 * (δ + 1)) * ((n + 1) + 2)) := by
  intro h hh
  by_cases hh1 : h = 1
  · subst hh1
    exact one_mem_relBall (relGenSetZ D Dc) lam _
  obtain ⟨w, hwlet, hwval, hwavoid, hwlen, hwne⟩ :=
    exists_nontrivial_word_of_mem_relBall (enlargedY D hDc hsymm) lam hh
  obtain ⟨ps, hpslen, hpsgeo, hpsval, hpsavoid⟩ :=
    exists_pieces_of_enlargedWord D hDc hsymm w hwlet hwne
  let f : List (RelLetter G Λ) := [RelLetter.comp lam h⁻¹]
  let qs : List (List (RelLetter G Λ)) := ps ++ [f]
  have hhD : h ∈ D.fam lam := hh.1
  have hfgeo : ∀ v : G,
      IsGeodesicWord (relGenSetZ D Dc) v
        (v * RelLetter.listVal f) f := by
    intro v
    simpa only [f, listVal_cons, RelLetter.listVal_nil, RelLetter.val, mul_one] using
      (isGeodesicWord_singleton (relGenSetZ D Dc)
        (a := RelLetter.comp lam h⁻¹) (inv_mem hhD) (inv_ne_one.mpr hh1) v)
  have hqsgeo : ∀ q ∈ qs, ∀ v : G,
      IsGeodesicWord (relGenSetZ D Dc) v
        (v * RelLetter.listVal q) q := by
    intro q hq v
    rcases List.mem_append.mp hq with hq | hq
    · exact hpsgeo q hq v
    · have hqf : q = f := by simpa [qs] using hq
      subst hqf
      exact hfgeo v
  have hflat : qs.flatten = ps.flatten ++ [RelLetter.comp lam h⁻¹] := by
    simp [qs, f]
  have hclosed : RelLetter.listVal qs.flatten = 1 := by
    rw [hflat, listVal_append, hpsval, hwval]
    rw [listVal_cons, RelLetter.listVal_nil, mul_one]
    exact mul_inv_cancel h
  have hpoly : IsQuasiGeodesicPolygon (relGenSetZ D Dc) 1 0 qs.length 1
      qs.flatten :=
    isQuasiGeodesicPolygon_flatten (relGenSetZ D Dc) 1 qs hqsgeo hclosed
  have havoidZ : AvoidsFrom (relGenSetZ D Dc).fam lam ps.flatten 1 := by
    exact hpsavoid lam 1 hwavoid
  have hletZ : ∀ a ∈ ps.flatten, (relGenSetZ D Dc).IsLetter a := by
    intro a ha
    obtain ⟨q, hq, haq⟩ := List.mem_flatten.mp ha
    exact (hpsgeo q hq 1).1 a haq
  have hiso : IsIsolated (relGenSetZ D Dc).fam lam 1 qs.flatten
      ps.flatten.length := by
    rw [hflat]
    exact isIsolated_closing_of_avoidsFrom (relGenSetZ D Dc) lam hhD hletZ
      (by rw [hpsval, hwval]) havoidZ
  obtain ⟨k, hkcomp⟩ := hiso.1
  have hk : k = ps.flatten.length + 1 := by
    have hklt := hkcomp.1
    have hkle := hkcomp.2.1
    rw [hflat, List.length_append, List.length_singleton] at hkle
    omega
  subst k
  have hδZ : Hyperbolic.IsFourPointHyperbolic
      (relGenSetZ D Dc).alphabet.carrier δ := by
    rw [alphabet_carrier_relGenSetZ]
    exact hδ
  have hpoly' : IsQuasiGeodesicPolygon (relGenSetZ D Dc) 1
      ((0 : ℕ) : ℝ) qs.length 1 qs.flatten := by
    simpa only [Nat.cast_zero] using hpoly
  have hbound := isolatedComponentBound_nGon_of_fourPointHyperbolic
    (relGenSetZ D Dc) (relGenSetZ_base_inv_mem D hsymm) 0 hδZ qs.length 1
    qs.flatten hpoly' lam ps.flatten.length (ps.flatten.length + 1) hkcomp hiso
  have hspan :
      (vertex 1 qs.flatten ps.flatten.length)⁻¹ *
          vertex 1 qs.flatten (ps.flatten.length + 1) = h⁻¹ := by
    rw [hflat, vertex_append_of_le ps.flatten [RelLetter.comp lam h⁻¹] 1
      ps.flatten.length le_rfl, vertex_length, one_mul, hpsval, hwval]
    have hlast : ps.flatten.length + 1 =
        (ps.flatten ++ [RelLetter.comp lam h⁻¹]).length := by simp
    rw [hlast, vertex_length]
    rw [listVal_append, hpsval, hwval, listVal_cons, RelLetter.listVal_nil,
      mul_one]
    group
    rfl
  rw [hspan] at hbound
  have hbound' := relBall_inv (relGenSetZ D Dc) lam
    (relGenSetZ_base_inv_mem D hsymm) hbound
  rw [inv_inv] at hbound'
  refine relBall_mono_radius (relGenSetZ D Dc) lam ?_ hbound'
  have hqsn : qs.length ≤ n + 1 := by
    simp only [qs, List.length_append, List.length_singleton]
    rw [hpslen]
    omega
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.add_le_add_right hqsn 1) le_rfl)
    (Nat.add_le_add_right hqsn 2)

/-- **Osin, Lemma 5.8.**  Enlarging `X` to `Y` preserves local finiteness of
all relative metrics. -/
theorem relBall_enlargedY_finite (D : RelGenSet G Λ) {Dc : ℕ}
    (hDc : 1 ≤ Dc) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded) :
    ∀ (lam : Λ) (n : ℕ), ((enlargedY D hDc hsymm).relBall lam n).Finite := by
  obtain ⟨δ, hδ⟩ := exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  intro lam n
  exact (relBall_relGenSetZ_finite D hDc hemb.locallyFinite lam
      (((n + 1) + 1) * (25 * (δ + 1)) * ((n + 1) + 2))).subset
    (relBall_enlargedY_subset_relGenSetZ D hDc hsymm hδ lam n)

end OsinComponents
end GGT
end GroupApproximation
