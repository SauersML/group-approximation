import GroupApproximation.GGT.OsinTheorem54SepDistSuffix

/-!
# The suffix separates strictly less

The counting half of Lemma 5.10's inductive step.  Cutting a geodesic at the
first crossing `[n₀,k₀)`, the piece past `k₀` has a strictly smaller separating
count, which is what makes the induction on `sep` terminate.

The map is `a ↦ k₀ + a` on penetration indices.  It lands in the whole word's
index set — the component by `isComp_of_isComp_suffix`, the span by
`span_segment` (the spans are literally equal, so essentiality transfers by
rewriting), the coset by `vertex_segment` — and it is injective, being a shift.
It MISSES `n₀`, since every value is at least `k₀ > n₀`; so at the index `lam`
of the crossing the inclusion is proper and the count drops.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The suffix's penetration indices shift into the word's.** -/
theorem mem_sepIndexSet_of_suffix (D : RelGenSet G Λ) (Dc : ℕ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam mu : Λ}
    {n₀ k₀ a : ℕ} (hcross : IsComp lam w n₀ k₀)
    (ha : a ∈ sepIndexSet D mu Dc (vertex f w k₀) g
      ((w.drop k₀).take (w.length - k₀))) :
    k₀ + a ∈ sepIndexSet D mu Dc f g w := by
  obtain ⟨c, hc, ⟨⟨b, hEP⟩, hcc⟩⟩ := ha
  have hkw : k₀ ≤ w.length := hcross.2.1
  obtain ⟨hab, hbl, -, -, -⟩ := hEP.1
  have hlen : ((w.drop k₀).take (w.length - k₀)).length = w.length - k₀ :=
    length_segment w k₀ (w.length - k₀) (by omega)
  have hcompw : IsComp mu w (k₀ + a) (k₀ + b) :=
    isComp_of_isComp_suffix lam mu w hcross hEP.1
  have hsp := span_segment w f k₀ (w.length - k₀) a b (by omega) (by omega)
  have hspanw : (vertex f w (k₀ + a))⁻¹ * vertex f w (k₀ + b)
      ∉ D.relBall mu Dc := by
    rw [← hsp]
    exact hEP.2
  have hccw : c = QuotientGroup.mk (vertex f w (k₀ + a)) := by
    rw [hcc, vertex_segment w f k₀ (w.length - k₀) a (by omega)]
  exact ⟨c, ⟨w, k₀ + a, k₀ + b, hw, ⟨hcompw, hspanw⟩, hccw⟩,
    ⟨⟨k₀ + b, ⟨hcompw, hspanw⟩⟩, hccw⟩⟩

/-- **The shifted image of the suffix's index set sits inside the word's, and
misses `n₀`.** -/
theorem image_sepIndexSet_subset (D : RelGenSet G Λ) (Dc : ℕ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam mu : Λ}
    {n₀ k₀ : ℕ} (hcross : IsComp lam w n₀ k₀) :
    (fun a : ℕ => k₀ + a) ''
        sepIndexSet D mu Dc (vertex f w k₀) g
          ((w.drop k₀).take (w.length - k₀))
      ⊆ sepIndexSet D mu Dc f g w := by
  rintro n ⟨a, ha, rfl⟩
  exact mem_sepIndexSet_of_suffix D Dc hw hcross ha

/-- **The count does not increase**, at every index. -/
theorem ncard_sepIndexSet_suffix_le (D : RelGenSet G Λ) (Dc : ℕ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam mu : Λ}
    {n₀ k₀ : ℕ} (hcross : IsComp lam w n₀ k₀) :
    (sepIndexSet D mu Dc (vertex f w k₀) g
        ((w.drop k₀).take (w.length - k₀))).ncard
      ≤ (sepIndexSet D mu Dc f g w).ncard := by
  have hinj : Set.InjOn (fun a : ℕ => k₀ + a)
      (sepIndexSet D mu Dc (vertex f w k₀) g
        ((w.drop k₀).take (w.length - k₀))) := by
    intro x _ y _ hxy
    have hxy' : k₀ + x = k₀ + y := hxy
    omega
  rw [← hinj.ncard_image]
  exact Set.ncard_le_ncard (image_sepIndexSet_subset D Dc hw hcross)
    (sepIndexSet_finite D mu Dc f g w)

/-- **At the crossing's own index the count strictly drops**, `n₀` lying in the
word's index set and in no shifted image. -/
theorem ncard_sepIndexSet_suffix_lt (D : RelGenSet G Λ) (Dc : ℕ) {f g : G}
    {w : List (RelLetter G Λ)} (hw : IsGeodesicWord D f g w) {lam : Λ}
    {n₀ k₀ : ℕ} (hcross : IsComp lam w n₀ k₀)
    (hess : (vertex f w n₀)⁻¹ * vertex f w k₀ ∉ D.relBall lam Dc) :
    (sepIndexSet D lam Dc (vertex f w k₀) g
        ((w.drop k₀).take (w.length - k₀))).ncard
      < (sepIndexSet D lam Dc f g w).ncard := by
  have hn0 : n₀ ∈ sepIndexSet D lam Dc f g w := by
    refine ⟨QuotientGroup.mk (vertex f w n₀),
      ⟨w, n₀, k₀, hw, ⟨hcross, hess⟩, rfl⟩, ⟨⟨k₀, ⟨hcross, hess⟩⟩, rfl⟩⟩
  have hnotmem : n₀ ∉ (fun a : ℕ => k₀ + a) ''
      sepIndexSet D lam Dc (vertex f w k₀) g
        ((w.drop k₀).take (w.length - k₀)) := by
    rintro ⟨a, -, hEq⟩
    have hEq' : k₀ + a = n₀ := hEq
    have hn0k : n₀ < k₀ := hcross.1
    omega
  have hinj : Set.InjOn (fun a : ℕ => k₀ + a)
      (sepIndexSet D lam Dc (vertex f w k₀) g
        ((w.drop k₀).take (w.length - k₀))) := by
    intro x _ y _ hxy
    have hxy' : k₀ + x = k₀ + y := hxy
    omega
  rw [← hinj.ncard_image]
  refine Set.ncard_lt_ncard ⟨image_sepIndexSet_subset D Dc hw hcross, ?_⟩
    (sepIndexSet_finite D lam Dc f g w)
  intro hsub
  exact hnotmem (hsub hn0)

end OsinComponents
end GGT
end GroupApproximation
