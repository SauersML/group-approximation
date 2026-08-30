import GroupApproximation.GGT.OsinTheorem54SepPolygon
import GroupApproximation.GGT.OsinTheorem54SepComponents

/-!
# Osin's Lemma 4.6: a geodesic enters a coset at the nearest point

If a geodesic `p` from `f` penetrates the coset `xH_λ` in a component `a`, then
the length of the part before `a` is exactly the distance from `f` to the coset.

That is the fact Lemma 4.9's splice runs on.  Two geodesics leaving the same
point and penetrating the same coset enter it after the same number of letters,
so the head of one can be joined to the tail of the other by a single
`H_λ`-edge and the result is again geodesic --- which transports an ESSENTIAL
penetration from one geodesic to the other without touching the component that
witnesses it.  No comparison of spans, and so no loss of depth.

## The proof

One inequality is the prefix bound: the first `i` letters spell the element
reached, so `d(f, vertexᵢ) ≤ i`, and `vertexᵢ` lies in the coset.

The other is where geodesy is spent.  Let `y` be any point of the coset.  From
`y` a single `H_λ`-letter reaches the component's EXIT vertex, since both lie in
the coset, so

  `|w| = d(f,g) ≤ d(f,y) + 1 + (|w| − k)`,

whence `k ≤ d(f,y) + 1`, and `i < k` gives `i ≤ d(f,y)`.  The exit vertex, not
the entrance, is what makes this work: leaving from the far end of the component
is what pays for the `+1`.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **On a geodesic word the index IS the distance.** -/
theorem wordDist_vertex_eq_index (D : RelGenSet G Λ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {i : ℕ}
    (hi : i ≤ w.length) :
    wordDist D.alphabet.carrier f (vertex f w i) = i := by
  have hle : wordDist D.alphabet.carrier f (vertex f w i) ≤ i := by
    have hpre : RelLetter.listVal (w.take i) = f⁻¹ * vertex f w i := by
      rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
    have h := wordNorm_listVal_le D (w.take i)
      (fun a ha => hw.1 a (List.take_subset i w ha))
    rw [hpre, List.length_take] at h
    have hd : wordDist D.alphabet.carrier f (vertex f w i)
        = wordNorm D.alphabet.carrier (f⁻¹ * vertex f w i) := rfl
    omega
  have hge := sub_le_wordDist_vertex D hw 0 i (Nat.zero_le _) hi
  rw [vertex_zero] at hge
  omega

/-- **Osin, Lemma 4.6.**  Every point of the penetrated coset is at least as far
from the origin as the component's entrance index. -/
theorem entrance_le_of_mem_coset (D : RelGenSet G Λ) (lam : Λ) {f g y : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {i k : ℕ}
    (hcomp : IsComp lam w i k)
    (hy : (QuotientGroup.mk y : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex f w i)) :
    i ≤ wordDist D.alphabet.carrier f y := by
  have hik : i < k := hcomp.1
  have hkw : k ≤ w.length := hcomp.2.1
  -- one `H_λ`-letter joins `y` to the component's exit vertex
  have hcos : (QuotientGroup.mk y : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex f w k) := by
    rw [hy]
    exact mk_vertex_eq_of_isComp D f hw.1 hcomp
  have hmem : y⁻¹ * vertex f w k ∈ D.fam lam := QuotientGroup.eq.mp hcos
  have hedge : wordDist D.alphabet.carrier y (vertex f w k) ≤ 1 := by
    show wordNorm D.alphabet.carrier (y⁻¹ * vertex f w k) ≤ 1
    exact wordNorm_le_one_of_mem (Or.inr (Set.mem_iUnion.mpr ⟨lam, hmem⟩))
  -- the tail of the geodesic reaches `g` in `|w| - k` letters
  have htail : wordDist D.alphabet.carrier (vertex f w k) g ≤ w.length - k := by
    have hsuf : RelLetter.listVal (w.drop k) = (vertex f w k)⁻¹ * g := by
      have hsplit : RelLetter.listVal (w.take k) * RelLetter.listVal (w.drop k)
          = RelLetter.listVal w := by
        rw [← listVal_append, List.take_append_drop]
      have hpre : RelLetter.listVal (w.take k) = f⁻¹ * vertex f w k := by
        rw [vertex_eq_mul_listVal_take, inv_mul_cancel_left]
      have hlw : RelLetter.listVal w = f⁻¹ * g := by
        rw [← hw.2.1]
        group
      rw [hpre, hlw] at hsplit
      calc RelLetter.listVal (w.drop k)
          = (f⁻¹ * vertex f w k)⁻¹ *
              ((f⁻¹ * vertex f w k) * RelLetter.listVal (w.drop k)) := by group
        _ = (f⁻¹ * vertex f w k)⁻¹ * (f⁻¹ * g) := by rw [hsplit]
        _ = (vertex f w k)⁻¹ * g := by group
    have h := wordNorm_listVal_le D (w.drop k)
      (fun a ha => hw.1 a (List.drop_subset k w ha))
    rw [hsuf, List.length_drop] at h
    have hd : wordDist D.alphabet.carrier (vertex f w k) g
        = wordNorm D.alphabet.carrier ((vertex f w k)⁻¹ * g) := rfl
    omega
  -- geodesy of `w` closes the gap
  have hfg : wordDist D.alphabet.carrier f g = w.length := hw.2.2.symm
  have h4 : wordDist D.alphabet.carrier f g
      ≤ wordDist D.alphabet.carrier f y
        + wordDist D.alphabet.carrier y (vertex f w k)
        + wordDist D.alphabet.carrier (vertex f w k) g := by
    have hA := wordDist_triangle D.alphabet.symmetricGenerating f y g
    have hB := wordDist_triangle D.alphabet.symmetricGenerating y
      (vertex f w k) g
    omega
  omega

/-- **Two geodesics from the same point enter a coset at the same index.**

This is the form Lemma 4.9's splice uses: the head of one geodesic and the tail
of the other have complementary lengths, so the spliced path is geodesic. -/
theorem entrance_eq_of_isComp (D : RelGenSet G Λ) (lam : Λ) {f g g' : G}
    {w w' : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w)
    (hw' : IsGeodesicWord D f g' w') {i k i' k' : ℕ}
    (hcomp : IsComp lam w i k) (hcomp' : IsComp lam w' i' k')
    (hsame : (QuotientGroup.mk (vertex f w i) : G ⧸ D.fam lam)
      = QuotientGroup.mk (vertex f w' i')) :
    i = i' := by
  have hiw : i ≤ w.length := by
    have hlt := hcomp.1
    have hle := hcomp.2.1
    omega
  have hiw' : i' ≤ w'.length := by
    have hlt' := hcomp'.1
    have hle' := hcomp'.2.1
    omega
  have h1 := entrance_le_of_mem_coset D lam hw hcomp hsame.symm
  have h2 := entrance_le_of_mem_coset D lam hw' hcomp' hsame
  rw [wordDist_vertex_eq_index D hw' hiw'] at h1
  rw [wordDist_vertex_eq_index D hw hiw] at h2
  omega

end OsinComponents
end GGT
end GroupApproximation
