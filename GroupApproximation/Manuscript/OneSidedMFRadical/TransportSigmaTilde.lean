import GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction

/-!
# `σ̃(g) = [Ad(V_n(g))]_n`, the printed corona homomorphism of `thm:transport`

`non_mf_groups_exist.tex`, the rewritten proof of Theorem `thm:transport`:

> For unitaries `A, B`, `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`, where the norm on the
> left is the operator norm on the Hilbert space `(M_{d_n}(ℂ), ‖·‖₂)`, so the
> maps `Ad(V_n(g))` are asymptotically multiplicative in operator norm and
> `σ̃(g) = [Ad(V_n(g))]_n ∈ U(𝓑)`, `𝓑 = ∏_n B(M_{d_n}(ℂ)) / ⊕_n B(M_{d_n}(ℂ))`,
> is a homomorphism, where `B(M_{d_n}(ℂ))` denotes the operators on the
> Hilbert--Schmidt Hilbert space.  The algebra `𝓑` is a norm matrix corona
> with coordinate sizes `d_n²` after a choice of matrix units.

`Manuscript/OneSidedMFRadical/HilbertSchmidtAdMatrix.lean` supplied the choice
of matrix units and the displayed estimate.  This file is the sentence that
follows from them: `𝓑` is the norm matrix corona over the square models, and
`σ̃` is a homomorphism into its unitary group.

The multiplicative defect of `(Ad(V_n))` does not merely become small, it
becomes null: `‖Ad(V_n(gh)) − Ad(V_n(g))Ad(V_n(h))‖ ≤ 2‖V_n(gh) − V_n(g)V_n(h)‖`
by the printed estimate, because `Ad` is multiplicative on the nose
(`adMatrix_mul`), and the right side tends to `0`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportSigmaTilde

open Filter Matrix Topology
open HilbertSchmidtAdMatrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} [Group G] (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
  (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)

/-- **`Ad(V_n(g))`, coordinatewise, as a unitary of `M_{d_n²}(ℂ)`.** -/
def adUnitary (g : G) (n : ℕ) : Matrix.unitaryGroup (sqModel (X n)) ℂ :=
  ⟨adMatrix (X n) (V n g), adMatrix_mem_unitary (X n) (V n g).2⟩

omit [Group G] [∀ n, Nonempty (X n)] in
@[simp] theorem adUnitary_coe (g : G) (n : ℕ) :
    ((adUnitary X V g n : Matrix.unitaryGroup (sqModel (X n)) ℂ) :
        Matrix (sqModel (X n)) (sqModel (X n)) ℂ)
      = adMatrix (X n) (V n g) := rfl

/-- **"the maps `Ad(V_n(g))` are asymptotically multiplicative in operator
norm".**  The defect does not merely stay small: it vanishes, because `Ad` is
multiplicative on the nose and the printed estimate is `2‖A − B‖`. -/
theorem tendsto_adMatrix_defect
    (hmul : ∀ g h : G, Tendsto (fun n ↦
      ‖(V n (g * h) : Matrix (X n) (X n) ℂ)
        - (V n g : Matrix (X n) (X n) ℂ) * (V n h : Matrix (X n) (X n) ℂ)‖)
      atTop (nhds 0)) (g h : G) :
    Tendsto (fun n ↦ ‖adMatrix (X n) (V n (g * h))
        - adMatrix (X n) (V n g) * adMatrix (X n) (V n h)‖)
      atTop (nhds 0) := by
  have hbound : ∀ n, ‖adMatrix (X n) (V n (g * h))
      - adMatrix (X n) (V n g) * adMatrix (X n) (V n h)‖
      ≤ 2 * ‖(V n (g * h) : Matrix (X n) (X n) ℂ)
        - (V n g : Matrix (X n) (X n) ℂ) *
          (V n h : Matrix (X n) (X n) ℂ)‖ := by
    intro n
    have hcard : 0 < Fintype.card (X n) := Fintype.card_pos
    have hA : ‖(V n (g * h) : Matrix (X n) (X n) ℂ)‖ ≤ 1 :=
      le_of_eq (CStarRing.norm_of_mem_unitary (V n (g * h)).2)
    have hB : ‖(V n g : Matrix (X n) (X n) ℂ) *
        (V n h : Matrix (X n) (X n) ℂ)‖ ≤ 1 :=
      le_of_eq (CStarRing.norm_of_mem_unitary (mul_mem (V n g).2 (V n h).2))
    have h := norm_adMatrix_sub_le (X n) hcard hA hB
    rwa [adMatrix_mul] at h
  refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
  simpa using (hmul g h).const_mul 2

/-- **`σ̃(g) = [Ad(V_n(g))]_n`**, the printed homomorphism into the unitary
group of the corona `𝓑` over the square models. -/
def sigmaTilde
    (hmul : ∀ g h : G, Tendsto (fun n ↦
      ‖(V n (g * h) : Matrix (X n) (X n) ℂ)
        - (V n g : Matrix (X n) (X n) ℂ) * (V n h : Matrix (X n) (X n) ℂ)‖)
      atTop (nhds 0)) :
    G →* unitary (NormMatrixCStarCorona (fun n ↦ sqModel (X n))) :=
  MonoidHom.mk'
    (fun g ↦ unitarySequenceToCorona (fun n ↦ sqModel (X n)) (adUnitary X V g))
    (by
      intro g h
      rw [← map_mul]
      refine Subtype.ext ?_
      show normMatrixCStarCoronaMk (fun n ↦ sqModel (X n))
          (unitarySequenceBounded (fun n ↦ sqModel (X n))
            (adUnitary X V (g * h)))
        = normMatrixCStarCoronaMk (fun n ↦ sqModel (X n))
          (unitarySequenceBounded (fun n ↦ sqModel (X n))
            (adUnitary X V g * adUnitary X V h))
      have hsub := map_sub (normMatrixCStarCoronaMk (fun n ↦ sqModel (X n)))
        (unitarySequenceBounded (fun n ↦ sqModel (X n))
          (adUnitary X V (g * h)))
        (unitarySequenceBounded (fun n ↦ sqModel (X n))
          (adUnitary X V g * adUnitary X V h))
      rw [← sub_eq_zero, ← hsub]
      refine (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ sqModel (X n))
        _).mpr ?_
      rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop]
      refine (tendsto_adMatrix_defect X V hmul g h).congr fun n ↦ ?_
      refine congrArg _ ?_
      rw [lp.coeFn_sub, Pi.sub_apply]
      rfl)

@[simp] theorem sigmaTilde_coe
    (hmul : ∀ g h : G, Tendsto (fun n ↦
      ‖(V n (g * h) : Matrix (X n) (X n) ℂ)
        - (V n g : Matrix (X n) (X n) ℂ) * (V n h : Matrix (X n) (X n) ℂ)‖)
      atTop (nhds 0)) (g : G) :
    ((sigmaTilde X V hmul g :
        unitary (NormMatrixCStarCorona (fun n ↦ sqModel (X n)))) :
      NormMatrixCStarCorona (fun n ↦ sqModel (X n)))
      = normMatrixCStarCoronaMk (fun n ↦ sqModel (X n))
          (unitarySequenceBounded (fun n ↦ sqModel (X n))
            (adUnitary X V g)) := rfl

end

end TransportSigmaTilde
end OneSidedMFRadical
end Manuscript
end GroupApproximation
