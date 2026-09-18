import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabQComplexProjection
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# The rank of a projection is a homotopy invariant

The second ingredient of `K₀(ℂ) = ℤ` in Cuntz's picture of Kasparov theory (J. Cuntz, *A new
look at KK-theory*, K-Theory 1 (1987), §2; Blackadar, *K-Theory for Operator Algebras*, 17.3):
the rank of a projection in a matrix algebra over `ℂ` is its trace, the trace is continuous and
natural-number valued on projections, hence constant along projection paths.  Consequently the
rank is well defined on homotopy classes of `⋆`-homomorphisms `ℂ → M_n(ℂ)`, and it is additive
on orthogonal sums (the Cuntz sum of classes).

* `nat_valued_path_const`: a continuous real path with natural-number values is constant
  (intermediate value theorem);
* `ProjectionPath.eq_of_trace`: an abstract continuous "trace" which is natural-number valued on
  projections is constant along projection paths;
* `matrix_trace_eq_finrank_range`: the trace of an idempotent matrix is the dimension of its
  range;
* `projectionRank`, `ProjectionPath.projectionRank_eq`, `projectionRank_add`;
* `homotopyClassRank : HomotopyClass ℂ (CStarMatrix (Fin n) (Fin n) ℂ) → ℕ`.

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-Complex, work order WO-TWWKK-C: `stabQ.Hom ℂ ℂ ≃+ ℤ`).
-/

open scoped ComplexOrder

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

/-- **A natural-number valued continuous path is constant.** -/
theorem nat_valued_path_const {f : ℝ → ℝ} (hf : Continuous f) {r : ℝ → ℕ}
    (hr : ∀ t, f t = (r t : ℝ)) : r 0 = r 1 := by
  by_contra hne
  rcases Nat.lt_or_ge (r 0) (r 1) with hlt | hge
  · have hle : r 0 + 1 ≤ r 1 := by omega
    have hle' : (r 0 : ℝ) + 1 ≤ (r 1 : ℝ) := by exact_mod_cast hle
    have hmem : (r 0 : ℝ) + 1 / 2 ∈ Set.Icc (f 0) (f 1) := by
      rw [hr 0, hr 1]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    obtain ⟨t, _, ht⟩ :=
      intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1) hf.continuousOn hmem
    rw [hr t] at ht
    have h2 : ((2 * r t : ℕ) : ℝ) = ((2 * r 0 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * r t = 2 * r 0 + 1 := by exact_mod_cast h2
    omega
  · have hle : r 1 + 1 ≤ r 0 := by omega
    have hle' : (r 1 : ℝ) + 1 ≤ (r 0 : ℝ) := by exact_mod_cast hle
    have hmem : (r 1 : ℝ) + 1 / 2 ∈ Set.Icc (f 1) (f 0) := by
      rw [hr 0, hr 1]
      exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
    obtain ⟨t, _, ht⟩ :=
      intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hf.continuousOn hmem
    rw [hr t] at ht
    have h2 : ((2 * r t : ℕ) : ℝ) = ((2 * r 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h3 : 2 * r t = 2 * r 1 + 1 := by exact_mod_cast h2
    omega

/-- **Trace invariance along projection paths.**  If `τ` is continuous and on every projection
takes the natural-number value `r p`, then `r` is constant along projection paths. -/
theorem ProjectionPath.eq_of_trace {B : Type u} [NonUnitalCStarAlgebra B] (τ : B → ℂ)
    (hτ : Continuous τ) (r : B → ℕ) (hr : ∀ p : B, IsStarProjection p → τ p = (r p : ℂ))
    {p q : B} (h : ProjectionPath p q) : r p = r q := by
  obtain ⟨P, hP, hproj, h0, h1⟩ := h
  have key : r (P 0) = r (P 1) :=
    nat_valued_path_const (f := fun t => (τ (P t)).re) (r := fun t => r (P t))
      (Complex.continuous_re.comp (hτ.comp hP))
      (fun t => by
        show (τ (P t)).re = (r (P t) : ℝ)
        rw [hr (P t) (hproj t), Complex.natCast_re])
  rw [← h0, ← h1]
  exact key

/-- **The trace of an idempotent matrix is the dimension of its range.** -/
theorem matrix_trace_eq_finrank_range {n : ℕ} {p : Matrix (Fin n) (Fin n) ℂ}
    (hp : IsIdempotentElem p) :
    p.trace = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' p)) : ℂ) := by
  have hL : IsIdempotentElem (Matrix.toLin' p) := by
    show Matrix.toLin' p * Matrix.toLin' p = Matrix.toLin' p
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hp.eq]
  rw [← Matrix.trace_toLin'_eq]
  exact LinearMap.IsProj.trace (LinearMap.IsIdempotentElem.isProj_range _ hL)

section Matrix

variable {n : ℕ}

/-- The **rank** of a matrix: the dimension of its range. -/
def projectionRank (p : CStarMatrix (Fin n) (Fin n) ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (Matrix.toLin' (CStarMatrix.ofMatrix.symm p)))

/-- The trace of an idempotent in `M_n(ℂ)` is its rank. -/
theorem trace_eq_projectionRank {p : CStarMatrix (Fin n) (Fin n) ℂ} (hp : IsIdempotentElem p) :
    (CStarMatrix.ofMatrix.symm p).trace = (projectionRank p : ℂ) := by
  have hp' : IsIdempotentElem (CStarMatrix.ofMatrix.symm p) := by
    show CStarMatrix.ofMatrix.symm p * CStarMatrix.ofMatrix.symm p = CStarMatrix.ofMatrix.symm p
    exact hp
  exact matrix_trace_eq_finrank_range hp'

/-- The trace is continuous on the C⋆-algebra `M_n(ℂ)`. -/
theorem continuous_matrixTrace :
    Continuous fun p : CStarMatrix (Fin n) (Fin n) ℂ => (CStarMatrix.ofMatrix.symm p).trace :=
  (CStarMatrix.ofMatrixL (m := Fin n) (n := Fin n) (A := ℂ)).symm.continuous.matrix_trace

/-- **The rank is constant along projection paths in `M_n(ℂ)`.** -/
theorem ProjectionPath.projectionRank_eq {p q : CStarMatrix (Fin n) (Fin n) ℂ}
    (h : ProjectionPath p q) : projectionRank p = projectionRank q :=
  h.eq_of_trace (fun x => (CStarMatrix.ofMatrix.symm x).trace) continuous_matrixTrace
    projectionRank (fun _ hx => trace_eq_projectionRank hx.isIdempotentElem)

/-- **The rank of an orthogonal sum of projections is the sum of the ranks.** -/
theorem projectionRank_add {p q : CStarMatrix (Fin n) (Fin n) ℂ} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) :
    projectionRank (p + q) = projectionRank p + projectionRank q := by
  have h := trace_eq_projectionRank (hp.add hq hpq).isIdempotentElem
  have hsum : (CStarMatrix.ofMatrix.symm (p + q)).trace
      = (CStarMatrix.ofMatrix.symm p).trace + (CStarMatrix.ofMatrix.symm q).trace :=
    Matrix.trace_add (CStarMatrix.ofMatrix.symm p) (CStarMatrix.ofMatrix.symm q)
  have key : ((projectionRank (p + q) : ℕ) : ℂ)
      = (projectionRank p : ℂ) + (projectionRank q : ℂ) := by
    rw [← trace_eq_projectionRank hp.isIdempotentElem,
      ← trace_eq_projectionRank hq.isIdempotentElem, ← hsum]
    exact h.symm
  exact_mod_cast key

/-- The zero projection has rank zero. -/
theorem projectionRank_zero : projectionRank (0 : CStarMatrix (Fin n) (Fin n) ℂ) = 0 := by
  have h := trace_eq_projectionRank (IsIdempotentElem.zero :
    IsIdempotentElem (0 : CStarMatrix (Fin n) (Fin n) ℂ))
  have hz : (CStarMatrix.ofMatrix.symm (0 : CStarMatrix (Fin n) (Fin n) ℂ)).trace = 0 :=
    Matrix.trace_zero (Fin n) ℂ
  have key : ((projectionRank (0 : CStarMatrix (Fin n) (Fin n) ℂ) : ℕ) : ℂ) = 0 :=
    h.symm.trans hz
  exact_mod_cast key

/-- **The rank of a homotopy class** of `⋆`-homomorphisms `ℂ → M_n(ℂ)`: the rank of the image
of `1`. -/
def homotopyClassRank (x : HomotopyClass ℂ (CStarMatrix (Fin n) (Fin n) ℂ)) : ℕ :=
  Quot.lift (fun φ : ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ => projectionRank (φ 1))
    (fun φ ψ h => ((nHomotopic_iff_projectionPath φ ψ).mp h).projectionRank_eq) x

theorem homotopyClassRank_mk (φ : ℂ →⋆ₙₐ[ℂ] CStarMatrix (Fin n) (Fin n) ℂ) :
    homotopyClassRank (HomotopyClass.mk φ) = projectionRank (φ 1) :=
  rfl

theorem homotopyClassRank_projectionClass (p : CStarMatrix (Fin n) (Fin n) ℂ)
    (hp : IsStarProjection p) : homotopyClassRank (projectionClass p hp) = projectionRank p := by
  show projectionRank (complexHom p hp 1) = projectionRank p
  rw [complexHom_apply_one]

end Matrix

end

end GroupApproximation.Full.TWWKK
