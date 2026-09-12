import GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:transport` along the rewritten printed route

`non_mf_groups_exist.tex`, Theorem `thm:transport`:

> Let `L ≤ G` have property (T), and let `u ∈ G` satisfy `uLu⁻¹ ≤ L`.  Let
> `(V_n)` be an operator norm asymptotic representation of `G`.  Then
> `Ad(V(u))(𝒞₂(V,L)) = 𝒞₂(V,L)`.

with `𝒞₂(V,L)` the *Hilbert--Schmidt* asymptotic commutant, `sup_n ‖x_n‖₂ < ∞`
and `‖V_n(ℓ)x_n − x_nV_n(ℓ)‖₂ → 0`.  The closing sentences of the printed
proof are

> So `[U, P] = 0` and `‖[Ad(V_n(u)), P_n]‖ → 0`.  For `(x_n) ∈ 𝒞₂(V,L)`,
> `‖P_n Ad(V_n(u))^{±1}x_n − Ad(V_n(u))^{±1}x_n‖₂
>   ≤ ‖[P_n, Ad(V_n(u))^{±1}]‖ ‖x_n‖₂ + ‖P_nx_n − x_n‖₂ → 0`,
> so `Ad(V(u))^{±1}x ∈ 𝒞₂(V,L)` by the displayed equivalence.

This module carries them and assembles the theorem.  The route is:

* `Manuscript/OneSidedMFRadical/HilbertSchmidtAdMatrix.lean` — the printed
  choice of matrix units and `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`;
* `HilbertSchmidtOperatorAction.lean` — the action `M x` and `‖M x‖₂ ≤ ‖M‖‖x‖₂`;
* `TransportSigmaTilde.lean` — `σ̃(g) = [Ad(V_n(g))]_n ∈ U(𝓑)`;
* `TransportKazhdanProjection.lean` — `P`, `P_n`, and
  `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`;
* `TransportProjectionCommutation.lean` — `[U, P] = 0`;
* `TransportProjectionCharacterization.lean` — the printed
  `(x_n) ∈ 𝒞₂(V,L) ↔ ‖P_nx_n − x_n‖₂ → 0`.

`Manuscript/OneSidedMFRadical/TransportCommutantEquality.lean`, which carries
the earlier operator-norm reading of `𝒞₂`, is untouched; its
`boundedHSCommutant` is contained in the printed `printedCTwo`
(`TransportPrintedCommutant.boundedHSCommutant_subset`), so the statement
proved here is the stronger one.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TransportPrintedRoute

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open HilbertSchmidtAdMatrix HilbertSchmidtOperatorAction TransportSigmaTilde
open TransportKazhdanProjection TransportProjectionCommutation
open TransportProjectionCharacterization TransportPrintedCommutant
open KazhdanAsymptoticCommutant KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `‖·‖₂` is unchanged by `Ad(W)` for any unitary `W`. -/
theorem hsNorm_applyOp_adMatrix_unitary (Y : FiniteModel) {W : Matrix Y Y ℂ}
    (hW : W ∈ Matrix.unitaryGroup Y ℂ) (a : Matrix Y Y ℂ) :
    hsNorm Y (applyOp Y (adMatrix Y W) a) = hsNorm Y a := by
  rw [applyOp_adMatrix]
  exact PrelimNotation.hsNorm_unitary_mul_mul Y hW
    (conjTranspose_mem_unitaryGroup hW) a

variable {G : Type} [Group G] (B : OpAlmostRepresentation G)
  [∀ n, Nonempty (B.model n)] (L : Subgroup G) (KD : KazhdanData ↥L)
  (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
  (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n)))

/-! ## `‖[Ad(V_n(u)), P_n]‖ → 0` -/

/-- **"So `[U, P] = 0` and `‖[Ad(V_n(u)), P_n]‖ → 0`."** -/
theorem tendsto_norm_commutator
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    {u : G} (hu : u ∈ compressionSet L) :
    Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * adMatrix (B.model n) (B.map n u)
        - adMatrix (B.model n) (B.map n u) *
          (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖) atTop (nhds 0) := by
  have hcommute := commute_sigmaB_projection B L KD f hf hu
  have hmul1 := map_mul (normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)))
    Pseq (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map u))
  have hmul2 := map_mul (normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)))
    (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map u)) Pseq
  have hsubmk := map_sub (normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)))
    (Pseq * unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map u))
    (unitarySequenceBounded (fun n ↦ sqModel (B.model n))
      (adUnitary B.model B.map u) * Pseq)
  have hzero : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n))
      (Pseq * unitarySequenceBounded (fun n ↦ sqModel (B.model n))
          (adUnitary B.model B.map u)
        - unitarySequenceBounded (fun n ↦ sqModel (B.model n))
          (adUnitary B.model B.map u) * Pseq) = 0 := by
    rw [hsubmk, hmul1, hmul2, hPmk, sigmaB_coe B u] at *
    rw [← hcommute, sub_self]
  have hnull := (normMatrixCStarCoronaMk_eq_zero_iff
    (fun n ↦ sqModel (B.model n)) _).mp hzero
  rw [IsNullMatrixSequence, Nat.cofinite_eq_atTop] at hnull
  refine hnull.congr fun n ↦ ?_
  refine congrArg _ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, lp.infty_coeFn_mul,
    Pi.mul_apply, Pi.mul_apply]
  rfl

/-! ## The closing estimate -/

omit [∀ n, Nonempty (B.model n)] in
/-- **"`‖P_n M x_n − M x_n‖₂ ≤ ‖[P_n, M]‖ ‖x_n‖₂ + ‖P_nx_n − x_n‖₂ → 0`."**
Stated for any coordinatewise operator `M` that is isometric in `‖·‖₂` and
asymptotically commutes with `P_n`, so that it applies to `Ad(V_n(u))` and to
its inverse alike. -/
theorem tendsto_hsNorm_applyOp_projection_sub_of
    (M : ∀ n, Matrix (sqModel (B.model n)) (sqModel (B.model n)) ℂ)
    (hiso : ∀ (n : ℕ) (a : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n) (applyOp (B.model n) (M n) a) = hsNorm (B.model n) a)
    (hcomm : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖) atTop (nhds 0))
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) {C : ℝ}
    (hC : ∀ n, hsNorm (B.model n) (x n) ≤ C)
    (hx : Tendsto (fun n ↦ hsNorm (B.model n)
      (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0)) :
    Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (M n) (x n))
          - applyOp (B.model n) (M n) (x n))) atTop (nhds 0) := by
  have hbound : ∀ n, hsNorm (B.model n)
      (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n)
          (applyOp (B.model n) (M n) (x n))
        - applyOp (B.model n) (M n) (x n))
      ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖ * C
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n) := by
    intro n
    have hcard : 0 < Fintype.card (B.model n) := B.modelNonempty n
    have hsplit : applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n)
          (applyOp (B.model n) (M n) (x n))
        - applyOp (B.model n) (M n) (x n)
        = applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n * M n
              - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n) (x n)
          + applyOp (B.model n) (M n)
              (applyOp (B.model n)
                ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                  (sqModel (B.model n)) ℂ) n) (x n) - x n) := by
      rw [applyOp_sub, applyOp_mul, applyOp_mul, applyOp_sub_right,
        sub_add_sub_cancel]
    have h1 : hsNorm (B.model n) (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n))
        ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n * M n
            - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * C :=
      le_trans (hsNorm_applyOp_le (B.model n) hcard _ _)
        (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
    have h2 : hsNorm (B.model n) (applyOp (B.model n) (M n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n))
        = hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n) := hiso n _
    rw [hsplit]
    have htri := hsNorm_add_le (B.model n) hcard
      (applyOp (B.model n)
        ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n))
      (applyOp (B.model n) (M n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n))
    linarith [htri, h1, h2.le, h2.ge]
  have hlim : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖ * C
      + hsNorm (B.model n) (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n))
      atTop (nhds 0) := by
    simpa using (hcomm.mul_const C).add hx
  exact squeeze_zero (fun n ↦ hsNorm_nonneg _ _) hbound hlim

/-! ## The endpoint -/

/-- **Theorem `thm:transport`, at the printed definition of `𝒞₂`, proved along
the printed route.** -/
theorem manuscriptPrintedTransportHS : PrintedTransportHS := by
  classical
  intro G _ L hT B u hu
  letI : ∀ n, Nonempty (B.model n) :=
    fun n ↦ Fintype.card_pos_iff.mp (B.modelNonempty n)
  obtain ⟨KD⟩ := exists_kazhdanData ↥L hT
  obtain ⟨f, Pseq, hf, hPproj, hPmk⟩ := exists_projectionData B L KD
  -- the two operators `Ad(V_n(u))^{±1}`
  have hisoA : ∀ (n : ℕ) (a : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n)
          (applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) a)
        = hsNorm (B.model n) a :=
    fun n a ↦ hsNorm_applyOp_adMatrix_unitary (B.model n) (B.map n u).2 a
  have hisoB : ∀ (n : ℕ) (a : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n)
          (applyOp (B.model n) (adMatrix (B.model n)
            ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) a)
        = hsNorm (B.model n) a :=
    fun n a ↦ hsNorm_applyOp_adMatrix_unitary (B.model n)
      (conjTranspose_mem_unitaryGroup (B.map n u).2) a
  have hcommA := tendsto_norm_commutator B L KD f Pseq hf hPmk hu
  have hcommB : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * adMatrix (B.model n)
            ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        - adMatrix (B.model n)
            ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖) atTop (nhds 0) := by
    refine hcommA.congr fun n ↦ ?_
    have hP : ((Pseq : ∀ n, Matrix (sqModel (B.model n))
        (sqModel (B.model n)) ℂ) n)ᴴ
        = (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n := (hPproj n).1
    have hstep : (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)
          - adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
        = (adMatrix (B.model n) (B.map n u) *
              (Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
            - (Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n *
              adMatrix (B.model n) (B.map n u))ᴴ := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_mul, adMatrix_conjTranspose, hP]
    rw [hstep, Matrix.l2_opNorm_conjTranspose, norm_sub_rev]
  refine image_eq_of_preserves B L u ?_ ?_
  · intro x hx
    obtain ⟨C, hC⟩ := hx.1
    refine ⟨isHSBounded_adjointSequence hx.1, ?_⟩
    have hxP := tendsto_hsNorm_applyOp_projection_sub B L KD f Pseq hf hPmk x hx
    have hgoal := tendsto_hsNorm_applyOp_projection_sub_of B Pseq
      (fun n ↦ adMatrix (B.model n) (B.map n u)) hisoA hcommA x hC hxP
    refine isHSAsymptoticallyCentral_of_tendsto B L KD f Pseq hf hPmk
      (adjointSequence B u x) (C := C) (fun n ↦ ?_) ?_
    · have h := hisoA n (x n)
      rw [applyOp_adMatrix_map B u n (x n)] at h
      calc hsNorm (B.model n) (adjointSequence B u x n)
          = hsNorm (B.model n)
            ((B.map n u : Matrix (B.model n) (B.model n) ℂ) * x n *
              (B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) := rfl
        _ = hsNorm (B.model n) (x n) := h
        _ ≤ C := hC n
    · refine hgoal.congr fun n ↦ ?_
      rw [applyOp_adMatrix_map B u n (x n)]
      rfl
  · intro x hx
    obtain ⟨C, hC⟩ := hx.1
    refine ⟨isHSBounded_coadjointSequence hx.1, ?_⟩
    have hxP := tendsto_hsNorm_applyOp_projection_sub B L KD f Pseq hf hPmk x hx
    have hgoal := tendsto_hsNorm_applyOp_projection_sub_of B Pseq
      (fun n ↦ adMatrix (B.model n)
        ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ))
      hisoB hcommB x hC hxP
    have hco : ∀ n, applyOp (B.model n) (adMatrix (B.model n)
        ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n)
        = coadjointSequence B u x n := by
      intro n
      rw [applyOp_adMatrix, Matrix.conjTranspose_conjTranspose]
      rfl
    refine isHSAsymptoticallyCentral_of_tendsto B L KD f Pseq hf hPmk
      (coadjointSequence B u x) (C := C) (fun n ↦ ?_) ?_
    · have h := hisoB n (x n)
      rw [hco n] at h
      rw [h]
      exact hC n
    · exact hgoal.congr fun n ↦ by rw [hco n]

end

end TransportPrintedRoute
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.TransportPrintedRoute.manuscriptPrintedTransportHS
