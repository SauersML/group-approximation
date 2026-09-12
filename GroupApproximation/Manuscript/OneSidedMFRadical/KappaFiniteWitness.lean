import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientMatrices
import GroupApproximation.KOne.KappaRelations

/-!
# A finite commutator witness for a trivial canonical K₁ class

For a countable purely infinite simple ring, a unit killed by the canonical
map to algebraic K₁ has a finite diagonal stabilization in the commutator
subgroup. The elementary subgroups at every finite rank lie in the respective
commutator subgroups. Their images in the direct limit form a directed union,
so membership in the defining stable elementary subgroup has a finite witness.

This is the stabilization input to the supported-unit compression proof.
The direct-limit equality is unpacked as eventual equality, not treated as
equality at the original rank.
-/

namespace GroupApproximation
namespace KappaProof

open AlgebraicK RankNElimination MFQuotientUnits

theorem map_mem_commutator {G H : Type*} [Group G] [Group H]
    (f : G →* H) {u : G} (hu : u ∈ commutator G) : f u ∈ commutator H := by
  have hle : (commutator G).map f ≤ commutator H := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  exact hle ⟨u, hu, rfl⟩

variable (R : Type) [Ring R] [Countable R]

/-- The ranks zero and one have no elementary generators; higher ranks use
the proved exact elementary/commutator equality. -/
theorem elementary_le_commutator (hR : IsPurelyInfiniteSimpleRing R) (n : ℕ) :
    elementaryGroup (Fin n) R ≤ commutator (Matrix (Fin n) (Fin n) R)ˣ := by
  by_cases hn : 2 ≤ n
  · exact le_of_eq (MFQuotientMatrices.mfHomKernel_matrixUnits_eq R hR n hn).2.symm
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact (hij (Fin.ext (by have hi := i.isLt; have hj := j.isLt; omega))).elim

/-- Every trivial canonical K₁ class is represented by a commutator-subgroup
matrix after some finite stabilization. -/
theorem exists_diagonal_mem_commutator (hR : IsPurelyInfiniteSimpleRing R)
    (u : Rˣ) (hu : kappa R u = 1) :
    ∃ (n : ℕ) (hn : 0 < n),
      diagAt (⟨0, hn⟩ : Fin n) u ∈ commutator (Matrix (Fin n) (Fin n) R)ˣ := by
  let D : ℕ → Subgroup (ClassicalGLColim R) := fun n =>
    (commutator (Matrix (Fin n) (Fin n) R)ˣ).map (glColimOf R n)
  have hmono : Monotone D := by
    intro n m hnm z hz
    obtain ⟨v, hv, rfl⟩ := hz
    refine ⟨glStab R n m hnm v, map_mem_commutator _ hv, ?_⟩
    exact glColimOf_glStab (R := R) hnm v
  have hle : elementaryColim R ≤ ⨆ n, D n := by
    apply iSup_le
    intro n
    exact (Subgroup.map_mono (elementary_le_commutator R hR n)).trans (le_iSup D n)
  have hmem := hle ((kappa_eq_one_iff R u).mp hu)
  obtain ⟨n, hn⟩ := (Subgroup.mem_iSup_of_directed hmono.directed_le).mp hmem
  obtain ⟨v, hv, heq⟩ := hn
  have hrel : ∃ (m : ℕ) (hnm : n ≤ m) (h1m : 1 ≤ m),
      glStab R n m hnm v = glStab R 1 m h1m (unitsToGLOne R u) :=
    Quotient.exact heq
  obtain ⟨m, hnm, h1m, hvm⟩ := hrel
  refine ⟨m, by omega, ?_⟩
  rw [← glStab_one_eq_diagAt m (by omega) h1m u, ← hvm]
  exact map_mem_commutator (glStab R n m hnm) hv

end KappaProof
end GroupApproximation

#audit_axioms GroupApproximation.KappaProof.exists_diagonal_mem_commutator
