import GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.TailSequence
import GroupApproximation.Meta.AxiomGuard

/-!
# The unital ⋆-homomorphism into the tracial matrix quotient (lane nm-tww-06, part 2)

`tailHom M N l hl a` is the class of `(φ_{n+N} a)_n` in
`TracialMatrixQuotient (tailSpace M N) l`, for any filter `l ≤ atTop`.

* Linearity and unitality hold exactly (`tailSeq_add`, `tailSeq_smul`,
  `tailSeq_one`).
* `⋆` is `tailSeq_star`, which comes from `Quasidiagonal.ucp_map_star`.
* Multiplicativity: the defect `tailSeq (a b) - tailSeq a * tailSeq b` is
  `‖·‖₂`-null along `atTop`, hence along `l`
  (`tendsto_hsNorm_tailSeq_mul`).  So its class vanishes by
  `tracialMatrixQuotientMk_eq_zero_iff`.

The quotient needs nonempty models, so this file assumes
`[∀ n, Nonempty (tailSpace M N n)]`.  `exists_tail_card_pos` supplies it once
`τ 1 = 1`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AmenableUltraHom

open Filter

universe u

noncomputable section

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
variable (M : Quasidiagonal.AmenableTraceModel τ) (N : ℕ)
variable [∀ n, Nonempty (tailSpace M N n)]

theorem tailSeq_one : tailSeq M N 1 = 1 := by
  refine lp.ext (funext fun n ↦ ?_)
  change M.map (n + N) 1 = 1
  exact M.map_one (n + N)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailSeq_one

/-- **The model as a unital ⋆-homomorphism into the tracial matrix
quotient**, at any filter finer than `atTop`. -/
def tailHom (l : Filter ℕ) (hl : l ≤ atTop) :
    A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient (tailSpace M N) l where
  toFun a := TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
    (tailSeq M N a)
  map_one' := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
      (tailSeq M N 1) = 1
    rw [tailSeq_one]
    exact map_one (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l)
  map_mul' a b := by
    have hzero : TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l
        (tailSeq M N (a * b) - tailSeq M N a * tailSeq M N b) = 0 :=
      (TracialUltraproduct.tracialMatrixQuotientMk_eq_zero_iff (tailSpace M N) l
        _).mpr ((tendsto_hsNorm_tailSeq_mul M N a b).mono_left hl)
    rw [map_sub, map_mul, sub_eq_zero] at hzero
    exact hzero
  map_zero' := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
      (tailSeq M N 0) = 0
    rw [tailSeq_zero]
    exact map_zero (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l)
  map_add' a b := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
        (tailSeq M N (a + b))
      = TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
          (tailSeq M N a)
        + TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
          (tailSeq M N b)
    rw [tailSeq_add]
    exact map_add (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l) _ _
  commutes' z := by
    have hseq : tailSeq M N (algebraMap ℂ A z) = z • tailSeq M N 1 := by
      rw [Algebra.algebraMap_eq_smul_one (A := A) z, tailSeq_smul]
    calc TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N (algebraMap ℂ A z))
        = TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (z • tailSeq M N 1) := by rw [hseq]
      _ = z • TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l (tailSeq M N 1) := map_smul (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l) z _
      _ = z • (1 : TracialUltraproduct.TracialMatrixQuotient (tailSpace M N) l) := by
        rw [tailSeq_one, map_one]
      _ = algebraMap ℂ (TracialUltraproduct.TracialMatrixQuotient (tailSpace M N) l) z :=
        (Algebra.algebraMap_eq_smul_one z).symm
  map_star' a := by
    show TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
        (tailSeq M N (star a))
      = star (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l
          (tailSeq M N a))
    rw [tailSeq_star]
    exact map_star (TracialUltraproduct.tracialMatrixQuotientQuotient (tailSpace M N) l) _

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailHom

theorem tailHom_apply (l : Filter ℕ) (hl : l ≤ atTop) (a : A) :
    tailHom M N l hl a
      = TracialUltraproduct.tracialMatrixQuotientMk (tailSpace M N) l
          (tailSeq M N a) :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AmenableUltraHom.tailHom_apply

end

end AmenableUltraHom
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
