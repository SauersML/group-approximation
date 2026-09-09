import GroupApproximation.KOne.DiagonalGroupNormalizer
import GroupApproximation.Meta.AxiomGuard

/-!
# Khanh--Thanh Lemma 4.1: `GL_n(R) = E_n(R) D_n(F)` from scalar surjectivity

`non_mf_groups_exist.tex`, proof of `cor:leavitt-mf-quotient`, cites
Khanh--Thanh for `GL_d(R) = EL_d(R)D_d(k)`.  Their paper (arXiv:2607.10351,
*Matrix generators for the unit groups of `L_K(1,d)`*) derives that from their
Lemma 4.1, and this module is that lemma:

> **4.1(i)** If `c ∈ [R^×, R^×]` then `diag(c, 1, …, 1) ∈ E_n(R)`.
>
> **4.1(ii)** Let `F` be a central subfield of `R`.  If `F^× → R^×_ab` is
> surjective, then `GL_n(R) = E_n(R) D_n(F)`.

Clause (i) is already on the tree, hypothesis-free, as
`RankNElimination.diagAt_commutator_mem` (Whitehead's identity in a two-index
block).  Clause (ii) is proved here, over any nontrivial strongly divisible ring
--- strong division supplies the GE-property their statement assumes, through
`RankNElimination.exists_elementary_mul_diagonal`.

## What the hypothesis is, and what it is not

The surjectivity hypothesis appears below in its elementwise form: every unit of
`R` differs from a scalar by a commutator.  That is exactly "the map
`F^× → R^×_ab` induced by the inclusion is surjective", written without naming
the abelianization.

It is **not** proved here for `L_k(1,d)`, and it is the whole difficulty.
Khanh--Thanh obtain it from the Ara--Brustenga graph K-theory exact sequence,
which computes `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` and in particular says the
scalar classes exhaust it.  Using that route to prove the decomposition, and
then the decomposition to compute `K₁`, would be circular; the repository's own
route to the same hypothesis is `MatrixDiagonalization.ScalarReduction`, whose
degree-zero half is `Leavitt/AryDegreeZeroUnits.lean` and whose remaining half
is the narrow-window kill.

## Why this supersedes the ad-hoc reduction

`Manuscript/OneSidedMFRadical/KhanhThanhDiagonalDecomposition.lean` reduces the
printed decomposition to a statement about `diag(u,1,…,1)` at one coordinate.
The lemma below is the source's own reduction, at every rank, over any strongly
divisible ring, and with the hypothesis in the form the K-theory actually
delivers.
-/

namespace GroupApproximation
namespace RankNElimination

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

/-! ### Single-coordinate diagonals -/

theorem diagAt_eq_diagonalUnit (l : ι) (u : Rˣ) :
    (diagAt l u : (Matrix ι ι R)ˣ) =
      diagonalUnit (fun i ↦ if i = l then u else 1) := by
  apply Units.ext
  rw [diagAt_val, diagonalUnit_val]
  congr 1
  funext i
  by_cases h : i = l <;> simp [h]

/-! ### Lemma 4.1(i), in the form the induction consumes -/

/-- **A diagonal all of whose entries are commutators is elementary.**

Khanh--Thanh's Lemma 4.1(i) says this for a single coordinate; the induction
over the support puts the coordinates together.  The hypothesis `∀ i, ∃ j, i ≠ j`
is their `n ≥ 2`. -/
theorem diagonalUnit_mem_elementaryGroup_of_forall_commutator
    (hne : ∀ i : ι, ∃ j : ι, i ≠ j) :
    ∀ (S : Finset ι) (c : ι → Rˣ), (∀ i, c i ∈ commutator Rˣ) →
      (∀ i, i ∉ S → c i = 1) → diagonalUnit c ∈ elementaryGroup ι R := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro c _ h1
      have hc1 : c = 1 := funext fun i ↦ h1 i (Finset.notMem_empty i)
      rw [hc1, show diagonalUnit (1 : ι → Rˣ) = 1 from map_one diagonalHom]
      exact one_mem _
  | insert a T haT ih =>
      intro c hcomm hsupp
      have hsplit : (fun i ↦ if i = a then c a else 1) *
          (fun i ↦ if i = a then (1 : Rˣ) else c i) = c := by
        funext i
        by_cases h : i = a
        · subst h
          simp
        · simp [h]
      have hone : diagonalUnit (fun i ↦ if i = a then c a else 1) ∈
          elementaryGroup ι R := by
        obtain ⟨j, hj⟩ := hne a
        rw [← diagAt_eq_diagonalUnit]
        exact diagAt_commutator_mem a j hj (hcomm a)
      have hrest : diagonalUnit (fun i ↦ if i = a then (1 : Rˣ) else c i) ∈
          elementaryGroup ι R := by
        refine ih _ (fun i ↦ ?_) (fun i hi ↦ ?_)
        · by_cases h : i = a
          · simp [h]
          · simpa [h] using hcomm i
        · by_cases h : i = a
          · simp [h]
          · have : i ∉ insert a T := by
              simp only [Finset.mem_insert, not_or]
              exact ⟨h, hi⟩
            simp [h, hsupp i this]
      have hmul : diagonalUnit c =
          diagonalUnit (fun i ↦ if i = a then c a else 1) *
            diagonalUnit (fun i ↦ if i = a then (1 : Rˣ) else c i) := by
        have hm := map_mul (diagonalHom (ι := ι) (R := R))
          (fun i ↦ if i = a then c a else 1)
          (fun i ↦ if i = a then (1 : Rˣ) else c i)
        rw [hsplit] at hm
        exact hm
      rw [hmul]
      exact mul_mem hone hrest

/-! ### Lemma 4.1(ii) -/

section Scalar

variable {k : Type*} [Field k]

/-- **Khanh--Thanh Lemma 4.1(ii)**: over a nontrivial strongly divisible ring,
if every unit differs from a scalar by a commutator, then every invertible
matrix is an elementary matrix times a diagonal matrix with scalar entries.

The strong division hypothesis supplies their GE-property, through
`exists_elementary_mul_diagonal`; the normalization clause of their proof is
`diagonalGroup_le_normalizer` and is not needed in this formulation, because the
elementary factor is produced on the left already. -/
theorem exists_elementary_mul_scalarDiagonal [Nontrivial R]
    (hdiv : HasSingleSandwichDivision R) (hne : ∀ i : ι, ∃ j : ι, i ≠ j)
    (f : k →+* R)
    (hsurj : ∀ u : Rˣ, ∃ a : kˣ,
      u * (Units.map (f : k →* R) a)⁻¹ ∈ commutator Rˣ)
    (l : ι) (A : (Matrix ι ι R)ˣ) :
    ∃ E ∈ elementaryGroup ι R,
      ∃ C ∈ scalarDiagonalGroup (ι := ι) f, A = E * C := by
  classical
  obtain ⟨E₀, hE₀, D, hD, hA⟩ := exists_elementary_mul_diagonal hdiv A l
  obtain ⟨u, rfl⟩ := mem_diagonalGroup_iff.mp hD
  choose a ha using fun i ↦ hsurj (u i)
  set s : ι → Rˣ := fun i ↦ Units.map (f : k →* R) (a i) with hs
  set c : ι → Rˣ := fun i ↦ u i * (s i)⁻¹ with hc
  have hcs : c * s = u := by
    funext i
    show u i * (s i)⁻¹ * s i = u i
    group
  have hcomm : ∀ i, c i ∈ commutator Rˣ := ha
  have hsplit : diagonalUnit u = diagonalUnit c * diagonalUnit s := by
    rw [← hcs]
    exact map_mul diagonalHom _ _
  refine ⟨E₀ * diagonalUnit c,
    mul_mem hE₀ (diagonalUnit_mem_elementaryGroup_of_forall_commutator hne
      Finset.univ c hcomm (fun i hi ↦ absurd (Finset.mem_univ i) hi)),
    diagonalUnit s, scalarDiagonalUnit_mem f a, ?_⟩
  rw [hA, hsplit]
  group

end Scalar

end RankNElimination
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.RankNElimination.diagAt_eq_diagonalUnit
#audit_axioms
  GroupApproximation.RankNElimination.diagonalUnit_mem_elementaryGroup_of_forall_commutator
#audit_axioms
  GroupApproximation.RankNElimination.exists_elementary_mul_scalarDiagonal
