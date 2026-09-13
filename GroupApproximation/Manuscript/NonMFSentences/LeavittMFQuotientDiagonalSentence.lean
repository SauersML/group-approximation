import GroupApproximation.Manuscript.NonMFSentences.LeavittKOneFormulaSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:leavitt-mf-quotient`: `GL_d(R) = EL_d(R)D_d(k)` and `K_1(R) ≅ k^×/(k^×)^{d-1}`

`non_mf_groups_exist.tex`, line 1307, the third sentence of the proof of the corollary
`\label{cor:leavitt-mf-quotient}` (Leavitt unit groups, tex 1297), census row `4321530b3fec`:

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the abelian group of
> diagonal matrices with entries in `k^×`, which normalizes `EL_d(R)`, and that
> `K_1(R) ≅ k^×/(k^×)^{d-1}` [KhanhThanh, proof of Theorem 7.2].

Here `R = L_k(1,d)` is `AryLeavitt.AryLeavittAlgebra k d`, and `D_d(k)` is
`KhanhThanhDiagonal.printedDiagonal k d`, the diagonal matrices of `GL_d(R)` whose entries are
the images of units of `k`.  Nothing is cited: every clause is proved in the repository, at
every field `k` (countability, assumed in the corollary, is not needed) and every `d ≥ 2`.

* `GL_d(R) = EL_d(R)D_d(k)`: from the closed matrix-entry form
  `KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity`
  (arity-`d` elimination, no literature input).
* `D_d(k)` consists of the diagonal matrices with entries in `k^×`: `mem_printedDiagonal_iff`.
* `D_d(k)` is abelian: `KhanhThanhDiagonal.printedDiagonal_mul_comm`.
* `D_d(k)` normalizes `EL_d(R)`: `KhanhThanhDiagonal.printedDiagonal_le_normalizer`.
* `K_1(R) ≅ k^×/(k^×)^{d-1}`: `LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula`
  (scalar surjectivity and the regularized-determinant scalar kernel).

## Endpoint

* `PrintedKhanhThanhSentence`, `manuscriptSentence_khanhThanhPrinted`: every clause of the
  sentence, with nothing assumed.
-/

namespace GroupApproximation
namespace LeavittMFQuotientDiagonalSentence

open AryLeavitt AlgebraicK Manuscript.OneSidedMFRadical

/-- **`D_d(k)` is the group of diagonal matrices with entries in `k^×`**: an element of
`GL_d(L_k(1,d))` lies in `KhanhThanhDiagonal.printedDiagonal k d` exactly when its matrix is
`diag(c_1,…,c_d)` with every `c_i ∈ k^×`. -/
theorem mem_printedDiagonal_iff (k : Type) [Field k] (d : ℕ)
    (C : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :
    C ∈ KhanhThanhDiagonal.printedDiagonal k d ↔
      ∃ c : Fin d → kˣ,
        (C : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
          Matrix.diagonal (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k))) := by
  constructor
  · intro hC
    exact KhanhThanhDiagonal.exists_scalar_entries_of_mem k d hC
  · rintro ⟨c, hc⟩
    obtain ⟨C', hC', hC'val⟩ := KhanhThanhDiagonal.exists_mem_printedDiagonal k d c
    rwa [show C = C' from Units.ext (hc.trans hC'val.symm)]

/-- **tex 1307, `cor:leavitt-mf-quotient`, proof, third sentence**, every clause:

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the abelian group of
> diagonal matrices with entries in `k^×`, which normalizes `EL_d(R)`, and that
> `K_1(R) ≅ k^×/(k^×)^{d-1}` [KhanhThanh, proof of Theorem 7.2].

for every field `k` and every `d ≥ 2`, with `R = L_k(1,d)` and
`D_d(k) = KhanhThanhDiagonal.printedDiagonal k d`.  The clauses, in order: every element of
`GL_d(R)` is an element of `EL_d(R)` times an element of `D_d(k)`; `D_d(k)` is the set of
diagonal matrices with entries in `k^×`; `D_d(k)` is abelian; `D_d(k)` normalizes
`EL_d(R)`; and `K_1(R) ≅ k^×/(k^×)^{d-1}`. -/
def PrintedKhanhThanhSentence : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d →
    (∀ M : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
      ∃ E ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
        ∃ D ∈ KhanhThanhDiagonal.printedDiagonal k d, M = E * D) ∧
    (∀ C : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ,
      C ∈ KhanhThanhDiagonal.printedDiagonal k d ↔
        ∃ c : Fin d → kˣ,
          (C : Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d)) =
            Matrix.diagonal (fun i ↦ algebraMap k (AryLeavittAlgebra k d) ((c i : k)))) ∧
    (∀ A ∈ KhanhThanhDiagonal.printedDiagonal k d,
      ∀ B ∈ KhanhThanhDiagonal.printedDiagonal k d, A * B = B * A) ∧
    KhanhThanhDiagonal.printedDiagonal k d ≤
      Subgroup.normalizer
        (elementaryGroup (Fin d) (AryLeavittAlgebra k d) :
          Set (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∧
    Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
      (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1)))

/-- **Closed carrier of the sentence.** -/
theorem manuscriptSentence_khanhThanhPrinted : PrintedKhanhThanhSentence := by
  intro k _ d hd
  refine ⟨fun M ↦ ?_, mem_printedDiagonal_iff k d,
    fun A hA B hB ↦ KhanhThanhDiagonal.printedDiagonal_mul_comm k d hA hB,
    KhanhThanhDiagonal.printedDiagonal_le_normalizer k d,
    LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula k d hd⟩
  obtain ⟨E, hE, c, hval⟩ :=
    KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity k d hd M
  obtain ⟨D, hD, hDval⟩ := KhanhThanhDiagonal.exists_mem_printedDiagonal k d c
  refine ⟨E, hE, D, hD, Units.ext ?_⟩
  rw [Units.val_mul, hDval]
  exact hval

end LeavittMFQuotientDiagonalSentence
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.LeavittMFQuotientDiagonalSentence.manuscriptSentence_khanhThanhPrinted
#audit_axioms GroupApproximation.LeavittMFQuotientDiagonalSentence.mem_printedDiagonal_iff
