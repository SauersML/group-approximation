import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Sofic.ProfiniteClosure

/-!
# Promoting profinite closedness through finite-index inclusions

A subgroup closed in a finite-index subgroup is closed in the ambient group.
The proof is completely finite-quotient based.  A quotient of the finite-index
subgroup is promoted by taking the normal core, in the ambient group, of its
kernel.  No topological completion is used.
-/

namespace GroupApproximation

noncomputable section

variable {G : Type} [Group G]

/-- Profinite closure is monotone. -/
theorem profiniteClosure_mono {A B : Subgroup G} (hAB : A ≤ B) :
    profiniteClosure A ≤ profiniteClosure B := by
  intro x hx Q _ _ q
  exact Subgroup.map_mono hAB (hx Q q)

/-- Every finite-index subgroup is profinitely closed. -/
theorem profiniteClosure_eq_of_finiteIndex (S : Subgroup G) [S.FiniteIndex] :
    profiniteClosure S = S := by
  apply le_antisymm
  · intro x hx
    let C := S.normalCore
    letI : C.Normal := inferInstance
    letI : C.FiniteIndex := inferInstance
    letI : Finite (G ⧸ C) := C.finite_quotient_of_finiteIndex
    let q : G →* G ⧸ C := QuotientGroup.mk' C
    have hxq : q x ∈ S.map q := hx (G ⧸ C) q
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp hxq
    have hdiff : s⁻¹ * x ∈ C := by
      exact (QuotientGroup.eq (s := C)).mp hsx
    have hdiffS : s⁻¹ * x ∈ S := S.normalCore_le hdiff
    have hxprod : x = s * (s⁻¹ * x) := by group
    rw [hxprod]
    exact S.mul_mem hs hdiffS
  · exact le_profiniteClosure S

variable (S : Subgroup G) [S.FiniteIndex]

/-- A subgroup closed in a finite-index subgroup remains closed after
inclusion into the ambient group. -/
theorem profiniteClosure_map_subtype_eq_of_closed
    (L : Subgroup S) (hL : profiniteClosure L = L) :
    profiniteClosure (L.map S.subtype) = L.map S.subtype := by
  apply le_antisymm
  · intro x hx
    have hxSclosure : x ∈ profiniteClosure S :=
      profiniteClosure_mono (show L.map S.subtype ≤ S from by
        intro y hy
        obtain ⟨l, -, rfl⟩ := hy
        exact l.property) hx
    have hxS : x ∈ S := by
      rw [profiniteClosure_eq_of_finiteIndex S] at hxSclosure
      exact hxSclosure
    let xs : S := ⟨x, hxS⟩
    have hxsClosure : xs ∈ profiniteClosure L := by
      intro Q _ _ q
      letI : q.ker.FiniteIndex :=
        finiteIndex_comap_of_normal q (⊥ : Subgroup Q)
      let N : Subgroup G := q.ker.map S.subtype
      letI : N.FiniteIndex := by
        refine ⟨?_⟩
        change (q.ker.map S.subtype).index ≠ 0
        rw [Subgroup.index_map_subtype]
        exact Nat.mul_ne_zero Subgroup.FiniteIndex.index_ne_zero
          Subgroup.FiniteIndex.index_ne_zero
      let C : Subgroup G := N.normalCore
      letI : C.Normal := inferInstance
      letI : C.FiniteIndex := inferInstance
      letI : Finite (G ⧸ C) := C.finite_quotient_of_finiteIndex
      let p : G →* G ⧸ C := QuotientGroup.mk' C
      have hxp : p x ∈ (L.map S.subtype).map p := hx (G ⧸ C) p
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxp
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      have hdiff : z⁻¹ * x ∈ C :=
        (QuotientGroup.eq (s := C)).mp hzx
      have hdiffN : z⁻¹ * x ∈ N := N.normalCore_le hdiff
      obtain ⟨n, hn, hnz⟩ := Subgroup.mem_map.mp hdiffN
      have hnS : n = y⁻¹ * xs := by
        apply Subtype.ext
        change (n : G) = (y : G)⁻¹ * x
        exact hnz.trans (congrArg (fun g : G => g⁻¹ * x) hyz).symm
      have hqdiff : q (y⁻¹ * xs) = 1 := by
        rw [← hnS]
        exact MonoidHom.mem_ker.mp hn
      have hqxy : q xs = q y := by
        rw [map_mul, map_inv] at hqdiff
        exact (inv_mul_eq_one.mp hqdiff).symm
      exact Subgroup.mem_map.mpr ⟨y, hy, hqxy.symm⟩
    rw [hL] at hxsClosure
    exact Subgroup.mem_map.mpr ⟨xs, hxsClosure, rfl⟩
  · exact le_profiniteClosure (L.map S.subtype)

end

end GroupApproximation
