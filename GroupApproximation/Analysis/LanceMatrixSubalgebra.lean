import GroupApproximation.Analysis.CStarMatrixFactorization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Matrices over a closed star subalgebra, and positivity permanence

Toward proof-ledger row `RE.05` (the Lance debt).  The Choi step of the
Arveson extension works with the star subalgebra of `CStarMatrix` whose
entries lie in a closed star subalgebra `C` of the ambient algebra — for the
Lance lane, matrices over `C*_λ(G)` inside matrices over `B(ℓ²(G))`.  This
file supplies:

* `matrixStarSubalgebra` — the entrywise subalgebra, with
  `isClosed_matrixStarSubalgebra`;
* `exists_entries_mem_factor` — **positivity permanence with a factorization**:
  a matrix that is positive in the ambient `CStarMatrix` order and has
  entries in `C` factors as `star N * N` with the entries of `N` again in
  `C`.  The square root is taken by the continuous functional calculus in
  the C⋆-algebra the closed entrywise subalgebra carries, and the spectra
  agree by spectral permanence, so ambient positivity descends.

This is the input that makes the Choi functional of a completely positive
map on `C` nonnegative on ambient positives, which is what the Krein
extension of `Analysis/StateExtension.lean` consumes.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

universe u

variable {A : Type u} [CStarAlgebra A]

/-- Matrices with entries in a star subalgebra form a star subalgebra of
`CStarMatrix`. -/
def matrixStarSubalgebra (C : StarSubalgebra ℂ A) (k : ℕ) :
    StarSubalgebra ℂ (CStarMatrix (Fin k) (Fin k) A) where
  carrier := {M | ∀ p q, M p q ∈ C}
  mul_mem' := by
    intro M N hM hN p q
    have h : (M * N) p q = ∑ r, M p r * N r q := Matrix.mul_apply
    rw [h]
    exact sum_mem fun r _ ↦ mul_mem (hM p r) (hN r q)
  add_mem' := by
    intro M N hM hN p q
    exact add_mem (hM p q) (hN p q)
  algebraMap_mem' := by
    intro z p q
    classical
    have h : (algebraMap ℂ (CStarMatrix (Fin k) (Fin k) A) z) p q
        = if p = q then algebraMap ℂ A z else 0 :=
      Matrix.algebraMap_matrix_apply
    rw [h]
    split
    · exact C.algebraMap_mem z
    · exact zero_mem C
  star_mem' := by
    intro M hM p q
    have h : (star M) p q = star (M q p) := rfl
    rw [h]
    exact star_mem (hM q p)

theorem mem_matrixStarSubalgebra_iff {C : StarSubalgebra ℂ A} {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) A} :
    M ∈ matrixStarSubalgebra C k ↔ ∀ p q, M p q ∈ C := Iff.rfl

/-- The entrywise subalgebra over a closed subalgebra is closed. -/
theorem isClosed_matrixStarSubalgebra (C : StarSubalgebra ℂ A) (k : ℕ)
    (hC : IsClosed (C : Set A)) :
    IsClosed ((matrixStarSubalgebra C k :
      Set (CStarMatrix (Fin k) (Fin k) A))) := by
  have h : (matrixStarSubalgebra C k :
      Set (CStarMatrix (Fin k) (Fin k) A))
      = ⋂ (p : Fin k) (q : Fin k),
          (fun M : CStarMatrix (Fin k) (Fin k) A ↦ M p q) ⁻¹' (C : Set A) := by
    ext M
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  refine isClosed_iInter fun p ↦ isClosed_iInter fun q ↦ ?_
  exact IsClosed.preimage ((continuous_apply q).comp (continuous_apply p)) hC

/-- **Positivity permanence with a factorization.**  A matrix over a closed
star subalgebra that is positive in the ambient order is `star N * N` for a
matrix `N` over the same subalgebra: take the square root inside the
C⋆-algebra the closed entrywise subalgebra carries, whose spectra agree with
the ambient ones by spectral permanence. -/
theorem exists_entries_mem_factor [PartialOrder A] [StarOrderedRing A]
    [NonnegSpectrumClass ℝ A]
    (C : StarSubalgebra ℂ A) (hC : IsClosed (C : Set A)) {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) A}
    (hmem : ∀ p q, M p q ∈ C) (hM : 0 ≤ M) :
    ∃ N : CStarMatrix (Fin k) (Fin k) A,
      (∀ p q, N p q ∈ C) ∧ M = star N * N := by
  classical
  haveI hclM : IsClosed ((matrixStarSubalgebra C k :
      Set (CStarMatrix (Fin k) (Fin k) A))) :=
    isClosed_matrixStarSubalgebra C k hC
  -- Instance search misses the selfadjoint real functional calculus on
  -- `CStarMatrix`, though the instance applies directly; register it.
  haveI : ContinuousFunctionalCalculus ℝ (CStarMatrix (Fin k) (Fin k) A)
      IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  haveI : NonnegSpectrumClass ℝ (CStarMatrix (Fin k) (Fin k) A) :=
    CStarAlgebra.instNonnegSpectrumClass'
  letI : CStarAlgebra ↥(matrixStarSubalgebra C k) :=
    { toNormedRing := inferInstance
      toStarRing := inferInstance
      toCompleteSpace := hclM.completeSpace_coe
      toCStarRing := inferInstance
      toNormedAlgebra := inferInstance
      toStarModule := inferInstance }
  letI pOrd : PartialOrder ↥(matrixStarSubalgebra C k) :=
    CStarAlgebra.spectralOrder _
  letI : StarOrderedRing ↥(matrixStarSubalgebra C k) :=
    CStarAlgebra.spectralOrderedRing _
  -- The subtype inherits the restricted ambient order through
  -- `Subtype.instLE`; shadow it so every `≤` below is the spectral order the
  -- factorization lemma expects.
  letI : LE ↥(matrixStarSubalgebra C k) := pOrd.toPreorder.toLE
  set Ms : ↥(matrixStarSubalgebra C k) := ⟨M, hmem⟩ with hMs_def
  have hsaA : IsSelfAdjoint M := .of_nonneg hM
  have hsaS : IsSelfAdjoint Ms := by
    refine Subtype.ext ?_
    show star M = M
    exact hsaA.star_eq
  have hspecC : spectrum ℂ Ms = spectrum ℂ M :=
    StarSubalgebra.spectrum_eq (S := matrixStarSubalgebra C k) (a := Ms)
  have hspecR : spectrum ℝ Ms = spectrum ℝ M := by
    rw [← spectrum.preimage_algebraMap (S := ℂ) (a := Ms),
      ← spectrum.preimage_algebraMap (S := ℂ) (a := M), hspecC]
  have h0S : (0 : ↥(matrixStarSubalgebra C k)) ≤ Ms := by
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Ms hsaS, hspecR]
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) M hsaA).mp hM
  obtain ⟨Ns, hNs⟩ := exists_star_mul_self_of_nonneg h0S
  refine ⟨(Ns : CStarMatrix (Fin k) (Fin k) A), fun p q ↦ Ns.2 p q, ?_⟩
  have h := congrArg Subtype.val hNs
  simpa using h

end CStarExactness
end GroupApproximation
