import GroupApproximation.GGT.OsinTheorem54SepSplice
import GroupApproximation.GGT.OsinTheorem54SepSegmentVertex

/-!
# A coset separating a stretch separates the whole

If `c` separates two vertices of a geodesic `w`, it separates the endpoints of
`w`.  Definition 4.3 names a geodesic between those two vertices that
essentially penetrates `c`; splice it into `w` and the result is a geodesic
between the endpoints carrying the SAME component, with the same span.

This is what the three sites that used to ask Lemma 4.8 for an essential
penetration now use instead.  The distinction matters: 4.8, as Osin states it,
gives penetration by an arbitrary geodesic and NOT essentiality --- two
geodesics through one coset enter it at the same index but with different
spans --- so essentiality has to be read off Definition 4.3's own witness, and
carried by construction rather than re-derived.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Separating a stretch of a geodesic separates its endpoints.** -/
theorem sepSet_of_sepSet_segment (D : RelGenSet G Λ) (lam : Λ) (Dc : ℕ)
    {f g : G} {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w)
    {k j : ℕ} (hkj : k ≤ j) (hj : j ≤ w.length) {c : G ⧸ D.fam lam}
    (hc : c ∈ sepSet D lam Dc (vertex f w k) (vertex f w j)) :
    c ∈ sepSet D lam Dc f g := by
  obtain ⟨u, a, b, hu, hEP, hcc⟩ := hc
  have hsplice := isGeodesicWord_splice D hw hkj hj hu
  have hab : a < b := hEP.1.1
  have hbu : b ≤ u.length := hEP.1.2.1
  have hba : b = a + 1 := isComp_eq_succ_of_isGeodesicWord D lam hu hEP.1
  have hkw : k ≤ w.length := by omega
  have hr : RelLetter.listVal u = (vertex f w k)⁻¹ * vertex f w j := by
    rw [← hu.2.1]
    group
  obtain ⟨hvpre, hvmid, hvsuf⟩ := vertex_splice f w u hkw hr
  -- the letter of the splice at `k + a` is the letter of `u` at `a`
  have hlen' : (w.take k ++ (u ++ w.drop j)).length
      = w.length := by
    have := hsplice.2.2
    have := hw.2.2
    omega
  have hau : a < u.length := by omega
  have hka : k + a < (w.take k ++ (u ++ w.drop j)).length := by
    rw [List.length_append, List.length_append, List.length_take,
      List.length_drop, Nat.min_eq_left hkw]
    omega
  have hmid : (w.take k ++ (u ++ w.drop j))[k + a]'hka = u[a]'hau := by
    rw [getElem_splice_mid w u (by omega) (by omega) hkw hka]
    exact getElem_congr_idx (by omega)
  -- so it is a component of the splice, single-lettered because the splice is
  -- geodesic, and its span is the span `u` already had
  have hcof : ((w.take k ++ (u ++ w.drop j))[k + a]'hka).IsCompOf lam := by
    rw [hmid]
    exact hEP.1.2.2.1 a le_rfl hab hau
  have hcomp' : IsComp lam (w.take k ++ (u ++ w.drop j)) (k + a) (k + a + 1) :=
    isComp_of_isCompOf_geodesic D lam hsplice hka hcof
  have hva : vertex f (w.take k ++ (u ++ w.drop j)) (k + a)
      = vertex (vertex f w k) u a := hvmid a (by omega)
  have hvb : vertex f (w.take k ++ (u ++ w.drop j)) (k + a + 1)
      = vertex (vertex f w k) u b := by
    rw [show k + a + 1 = k + b from by omega]
    exact hvmid b hbu
  refine ⟨w.take k ++ (u ++ w.drop j), k + a, k + a + 1, hsplice,
    ⟨hcomp', ?_⟩, ?_⟩
  · rw [hva, hvb]
    exact hEP.2
  · rw [hva]
    exact hcc

end OsinComponents
end GGT
end GroupApproximation
