import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ElementarySimplicity
import GroupApproximation.Leavitt.ElementaryTransvectionExtraction

/-!
# Diagonal elements in normal subgroups of elementary groups

This file closes the diagonal branch of root detection and then combines it
with the sparse and dense commutator extractions from
`ElementaryTransvectionExtraction`.  The resulting
`rootDetection_of_leavittFamily` is unconditional from the three ring inputs
already available for the binary Leavitt algebra: a Leavitt family, two-sided
division of every nonzero coefficient, and trivial central units.
-/

namespace GroupApproximation

open ElementarySimplicity

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The inverse of an invertible diagonal matrix is diagonal.  The proof is
valid over a noncommutative ring: the two matrix inverse identities provide the
two cancellation directions separately. -/
theorem matrixUnit_inv_offDiag_eq_zero
    (u : (Matrix ι ι R)ˣ)
    (hdiag : ∀ p q : ι, p ≠ q → (u : Matrix ι ι R) p q = 0)
    {p q : ι} (hpq : p ≠ q) :
    (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q) = 0 := by
  classical
  have hleft :
      (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p p) *
          (u : Matrix ι ι R) p p = 1 := by
    have hinv :
        (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
          (u : Matrix ι ι R)) = 1 := u.inv_mul
    have h := congrFun (congrFun hinv p) p
    rw [Matrix.mul_apply, Matrix.one_apply, if_pos rfl,
      Finset.sum_eq_single p] at h
    · exact h
    · intro k _ hkp
      rw [hdiag k p hkp, mul_zero]
    · exact fun hp ↦ (hp (Finset.mem_univ p)).elim
  have hright :
      (u : Matrix ι ι R) p p *
          (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q) = 0 := by
    have hinv :
        ((u : Matrix ι ι R) *
          ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) = 1 := u.mul_inv
    have h := congrFun (congrFun hinv p) q
    rw [Matrix.mul_apply, Matrix.one_apply, if_neg hpq,
      Finset.sum_eq_single p] at h
    · exact h
    · intro k _ hkp
      rw [hdiag p k (Ne.symm hkp), zero_mul]
    · exact fun hp ↦ (hp (Finset.mem_univ p)).elim
  calc
    (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q)
        = 1 * (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q) :=
          (one_mul _).symm
    _ = ((((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p p) *
          (u : Matrix ι ι R) p p) *
          (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q) := by rw [hleft]
    _ = (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p p) *
          ((u : Matrix ι ι R) p p *
            (((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) p q)) := by
              rw [mul_assoc]
    _ = 0 := by rw [hright, mul_zero]

/-- A nonidentity diagonal element of a normal subgroup contains a nonzero
elementary root.  Trivial central units rule out the only exceptional case:
a diagonal element commuting with every elementary root. -/
theorem exists_elGen_mem_of_diagonal
    (hcard : 3 ≤ Fintype.card ι)
    (hcentral : ∀ u : Rˣ,
      (∀ y : R, (u : R) * y = y * (u : R)) → u = 1)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) (hgne : g ≠ 1)
    (hdiag : ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    ∃ (i j : ι) (hij : i ≠ j) (a : R),
      a ≠ 0 ∧ elGen i j hij a ∈ N := by
  classical
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hcenter : Subgroup.center (elementaryGroup ι R) = ⊥ :=
    center_elementaryGroup_eq_bot_of_units hcentral
  have hgnotcenter : g ∉ Subgroup.center (elementaryGroup ι R) := by
    intro hgcenter
    have hgbot : g ∈ (⊥ : Subgroup (elementaryGroup ι R)) := by
      rw [← hcenter]
      exact hgcenter
    exact hgne (Subgroup.mem_bot.mp hgbot)
  have hnotcomm : ∃ z : elementaryGroup ι R,
      ElementarySimplicity.elMat g * ElementarySimplicity.elMat z ≠
        ElementarySimplicity.elMat z * ElementarySimplicity.elMat g := by
    by_contra hall
    push Not at hall
    apply hgnotcenter
    rw [Subgroup.mem_center_iff]
    intro z
    apply elMat_injective
    rw [elMat_mul, elMat_mul]
    exact (hall z).symm
  obtain ⟨z, hz⟩ := hnotcomm
  obtain ⟨i, j, hij, a, hsingle⟩ :=
    exists_noncommuting_single_of_not_central hcard
      (ElementarySimplicity.elMat g) hz
  let y : R := ElementarySimplicity.elMat g i i * a *
    ElementarySimplicity.elMat (g⁻¹) j j
  have hconj : conjSingle (g : (Matrix ι ι R)ˣ) i j a =
      Matrix.single i j y := by
    exact conjSingle_eq_single_of_concentrated (g : (Matrix ι ι R)ˣ) i j a
      (fun p hpi ↦ hdiag p i hpi)
      (fun q hqj ↦ matrixUnit_inv_offDiag_eq_zero
        (g : (Matrix ι ι R)ˣ) hdiag (Ne.symm hqj))
  have hya : y ≠ a := by
    intro hya
    apply hsingle
    have hinv :
        (ElementarySimplicity.elMat (g⁻¹) *
          ElementarySimplicity.elMat g) = 1 :=
      ElementarySimplicity.elMat_inv_mul g
    calc
      ElementarySimplicity.elMat g * Matrix.single i j a =
          (ElementarySimplicity.elMat g * Matrix.single i j a *
            ElementarySimplicity.elMat (g⁻¹)) *
              ElementarySimplicity.elMat g := by
                rw [mul_assoc, hinv, mul_one]
      _ = Matrix.single i j y * ElementarySimplicity.elMat g := by
        rw [← hconj]
        rfl
      _ = Matrix.single i j a * ElementarySimplicity.elMat g := by rw [hya]
  exact exists_elGen_mem_of_conjSingle_eq N hg hij hconj hya

/-- Consequently, a normal subgroup containing a nonidentity diagonal element
is the whole elementary group as soon as every nonzero coefficient admits a
two-sided unit sandwich. -/
theorem normal_eq_top_of_diagonal_mem
    (hcard : 3 ≤ Fintype.card ι)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hcentral : ∀ u : Rˣ,
      (∀ y : R, (u : R) * y = y * (u : R)) → u = 1)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) (hgne : g ≠ 1)
    (hdiag : ∀ p q : ι, p ≠ q →
      ElementarySimplicity.elMat g p q = 0) :
    N = ⊤ := by
  obtain ⟨i, j, hij, a, ha, hmem⟩ :=
    exists_elGen_mem_of_diagonal hcard hcentral N hg hgne hdiag
  exact elementaryGroup_normal_eq_top_of_elGen_mem hcard N hij hmem (hdiv a ha)

/-! ## Exhausting the diagonal, sparse, and dense cases -/

/-- **Unconditional root detection from the Leavitt ring inputs.**

Choose a nonidentity `g ∈ N`.  If `g` is diagonal, the centre calculation and
the line-preserving commutator above extract a root.  Otherwise choose a
nonzero off-diagonal entry `g_{li}`.  If the matching entry of `g⁻¹` vanishes,
`exists_elGen_mem_of_inv_entry_zero` applies.  If it is nonzero, use the same
two indices in both commuting roots; Leavitt coefficient separation kills the
forward scalar obstruction while preserving its reversal, and
`exists_elGen_mem_of_dense_entries` applies.  These cases are exhaustive and
do not invoke a normal-subgroup sandwich theorem. -/
theorem rootDetection_of_leavittFamily
    (hcard : 3 ≤ Fintype.card ι)
    (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hcentral : ∀ u : Rˣ,
      (∀ y : R, (u : R) * y = y * (u : R)) → u = 1) :
    RootDetection ι R := by
  intro N hN hNbot
  letI : N.Normal := hN
  obtain ⟨⟨g, hg⟩, hgne'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
  have hgne : g ≠ 1 := fun h ↦ hgne' (Subtype.ext h)
  by_cases hdiag : ∀ p q : ι, p ≠ q → ElementarySimplicity.elMat g p q = 0
  · exact exists_elGen_mem_of_diagonal hcard hcentral N hg hgne hdiag
  · push Not at hdiag
    obtain ⟨l, i, hli, hgi⟩ := hdiag
    by_cases hzero :
        (((g : (Matrix ι ι R)ˣ)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) l i = 0
    · exact exists_elGen_mem_of_inv_entry_zero hcard N hg hli hzero hgi
    · exact exists_elGen_mem_of_dense_entries hcard L hdiv N hg
        (i := i) (j := l) (k := i) (l := l)
        (Ne.symm hli) (Ne.symm hli) hli hli hzero hgi

/-- The corresponding generic simplicity theorem.  Unlike the earlier
conditional reduction, its root-detection premise is discharged by the direct
diagonal/sparse/dense case split. -/
theorem isSimpleGroup_of_leavittFamily_root_extraction
    (hcard : 3 ≤ Fintype.card ι)
    (L : LeavittFamily R)
    (hdiv : ∀ x : R, x ≠ 0 → ∃ a b : R, a * x * b = 1)
    (hcentral : ∀ u : Rˣ,
      (∀ y : R, (u : R) * y = y * (u : R)) → u = 1)
    (hne : Nontrivial (elementaryGroup ι R)) :
    IsSimpleGroup (elementaryGroup ι R) :=
  isSimpleGroup_of_rootDetection hcard hdiv hne
    (rootDetection_of_leavittFamily hcard L hdiv hcentral)

end GroupApproximation
