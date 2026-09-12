import GroupApproximation.Sofic.OmegaOperatorUltraproduct
import GroupApproximation.Sofic.OpAlmostRepresentation

/-!
# KT.09: `π(g) = [Ad U_n(g)]_ω` is a homomorphism into the unitaries of `B_ω`

The printed proof of `thm:kazhdan-transport` forms `B_ω = ∏_ω B(K_n)` and then
says, in one line, that the almost representation becomes an honest
representation there:

> `π(g) = [Ad U_n(g)]_ω` is a homomorphism `H → U(B_ω)`

That line is the entire reason for passing to an ultraproduct: the defect of an
almost representation is not zero at any stage, and it *is* zero in `B_ω`.  The
development had no counterpart to it, because it had no `B_ω`.

## The two halves, and why one of them needs no analysis

Multiplicativity is where the ultrafilter is used: `Ad` is exactly
multiplicative, so the defect of `π` at `(g,h)` is the class of
`Ad U_n(gh) - Ad U_n(g) Ad U_n(h)`, whose norms tend to zero along `atTop` by
`OpAlmostRepresentation.adjoint`, hence along any `ω` refining the cofinite
filter, hence the class is zero.

Unitarity is *exact* and needs no limit at all: `Ad U` is unitary at every
stage, so `star (adSeq g) * adSeq g = 1` already in `ℓ∞`, and the quotient map
is a ring homomorphism.

`π(1) = 1` then costs nothing either, and in particular no separate
"`U_n(1) → 1`" argument: `π(1)π(1) = π(1)` by multiplicativity, and `π(1)` is
invertible because it is unitary, so `π(1) = star π(1) * π(1) * π(1) = 1`.
An almost representation is not assumed to send `1` to `1`, and it does not
have to be.
-/

namespace GroupApproximation
namespace OmegaAlmostRepresentation

open Filter Matrix Topology
open UltrafilterLimit UltraproductModelConstruction OmegaOperatorUltraproduct
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The coordinate models of an almost representation are nonempty, which is
what the corona construction asks of them. -/
instance nonemptyModel (A : OpAlmostRepresentation G) (n : ℕ) :
    Nonempty (A.model n) :=
  Fintype.card_pos_iff.mp (A.modelNonempty n)

variable (A : OpAlmostRepresentation G) (ω : Ultrafilter ℕ)

/-! ## The sequence, and its exact unitarity -/

/-- `Ad U_n(g)`, as a uniformly bounded operator sequence.  The bound is `1`
at every stage because `Ad U` is unitary, not merely bounded. -/
def adSeq (g : G) : BoundedMatrixSequence (DblIdx A.model) :=
  ⟨fun n ↦ (A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ),
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      exact le_of_eq (CStarRing.norm_of_mem_unitary (A.adjoint.map n g).2)⟩⟩

@[simp] theorem adSeq_apply (g : G) (n : ℕ) :
    (adSeq A g : ∀ n, Matrix (DblIdx A.model n) (DblIdx A.model n) ℂ) n
      = (A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ) :=
  rfl

theorem adSeq_star_mul (g : G) : star (adSeq A g) * adSeq A g = 1 := by
  refine Subtype.ext (funext fun n ↦ ?_)
  show star ((A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ))
      * (A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ) = 1
  exact Unitary.star_mul_self_of_mem (A.adjoint.map n g).2

theorem adSeq_mul_star (g : G) : adSeq A g * star (adSeq A g) = 1 := by
  refine Subtype.ext (funext fun n ↦ ?_)
  show (A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ)
      * star ((A.adjoint.map n g : Matrix (A.adjoint.model n) (A.adjoint.model n) ℂ)) = 1
  exact Unitary.mul_star_self_of_mem (A.adjoint.map n g).2

/-! ## The class in `B_ω` -/

/-- **KT.09.**  The manuscript's `π(g) = [Ad U_n(g)]_ω`. -/
def piOmega (g : G) : OmegaAdjointCorona A.model ω :=
  omegaMk A.model ω (adSeq A g)

@[simp] theorem piOmega_def (g : G) :
    piOmega A ω g = omegaMk A.model ω (adSeq A g) := rfl

theorem omegaMk_star {Y : ℕ → FiniteModel} [∀ n, Nonempty (Y n)]
    (a : BoundedMatrixSequence (DblIdx Y)) :
    star (omegaMk Y ω a) = omegaMk Y ω (star a) :=
  filterMatrixCorona_star_mk (DblIdx Y) (ω : Filter ℕ) a

theorem piOmega_star_mul (g : G) :
    star (piOmega A ω g) * piOmega A ω g = 1 := by
  rw [piOmega_def, omegaMk_star, ← map_mul, adSeq_star_mul, map_one]

theorem piOmega_mul_star (g : G) :
    piOmega A ω g * star (piOmega A ω g) = 1 := by
  rw [piOmega_def, omegaMk_star, ← map_mul, adSeq_mul_star, map_one]

theorem piOmega_mem_unitary (g : G) :
    piOmega A ω g ∈ unitary (OmegaAdjointCorona A.model ω) :=
  Unitary.mem_iff.2 ⟨piOmega_star_mul A ω g, piOmega_mul_star A ω g⟩

/-! ## Multiplicativity: the one place the ultrafilter is used -/

/-- The adjoint defect vanishes along `atTop`; this is the almost
representation's own hypothesis, transported through `Ad`. -/
theorem tendsto_adjoint_defect (g h : G) :
    Tendsto (fun n ↦
        ‖(adSeq A (g * h) : ∀ n, Matrix (DblIdx A.model n) (DblIdx A.model n) ℂ) n
          - (adSeq A g : ∀ n, Matrix (DblIdx A.model n) (DblIdx A.model n) ℂ) n
            * (adSeq A h : ∀ n, Matrix (DblIdx A.model n) (DblIdx A.model n) ℂ) n‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    A.adjoint.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  exact lt_of_le_of_lt (hN n hn) (by linarith)

/-- **KT.09, multiplicativity.**  `Ad` is exactly multiplicative, so the defect
of `π` at `(g,h)` is the class of the almost representation's own defect, which
is null along every `ω` refining the cofinite filter. -/
theorem piOmega_mul (hω : (ω : Filter ℕ) ≤ cofinite) (g h : G) :
    piOmega A ω (g * h) = piOmega A ω g * piOmega A ω h := by
  have hle : (ω : Filter ℕ) ≤ atTop := by rwa [Nat.cofinite_eq_atTop] at hω
  have hnull : Tendsto (fun n ↦
      ‖((adSeq A (g * h) - adSeq A g * adSeq A h :
          BoundedMatrixSequence (DblIdx A.model)) :
        ∀ n, Matrix (DblIdx A.model n) (DblIdx A.model n) ℂ) n‖)
      (ω : Filter ℕ) (𝓝 0) :=
    (tendsto_adjoint_defect A g h).mono_left hle
  have hzero : omegaMk A.model ω (adSeq A (g * h))
      - omegaMk A.model ω (adSeq A g * adSeq A h) = 0 := by
    rw [← map_sub, omegaMk_eq_zero_iff]
    exact hnull
  rw [map_mul] at hzero
  exact sub_eq_zero.mp hzero

/-- **KT.09, the unit.**  No separate argument that `U_n(1)` tends to `1` is
needed: `π(1)` is idempotent by multiplicativity and invertible because it is
unitary. -/
theorem piOmega_one (hω : (ω : Filter ℕ) ≤ cofinite) :
    piOmega A ω 1 = 1 := by
  have hidem : piOmega A ω 1 * piOmega A ω 1 = piOmega A ω 1 := by
    rw [← piOmega_mul A ω hω, one_mul]
  calc piOmega A ω 1 = (star (piOmega A ω 1) * piOmega A ω 1) * piOmega A ω 1 := by
        rw [piOmega_star_mul, one_mul]
    _ = star (piOmega A ω 1) * (piOmega A ω 1 * piOmega A ω 1) := by
        rw [mul_assoc]
    _ = star (piOmega A ω 1) * piOmega A ω 1 := by rw [hidem]
    _ = 1 := piOmega_star_mul A ω 1

/-- **KT.09, as printed.**  `π(g) = [Ad U_n(g)]_ω` is a homomorphism
`G → U(B_ω)`.

This is the step that turns an almost representation into a representation.
The hypothesis is exactly the manuscript's: `ω` refines the cofinite filter,
i.e. `ω` is free. -/
def piHom (hω : (ω : Filter ℕ) ≤ cofinite) :
    G →* unitary (OmegaAdjointCorona A.model ω) where
  toFun g := ⟨piOmega A ω g, piOmega_mem_unitary A ω g⟩
  map_one' := Subtype.ext (piOmega_one A ω hω)
  map_mul' g h := Subtype.ext (piOmega_mul A ω hω g h)

@[simp] theorem piHom_apply (hω : (ω : Filter ℕ) ≤ cofinite) (g : G) :
    (piHom A ω hω g : OmegaAdjointCorona A.model ω) = piOmega A ω g := rfl

end

end OmegaAlmostRepresentation
end GroupApproximation
