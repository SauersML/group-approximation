import GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# Kazhdan transport in Hilbert--Schmidt norm: the printed estimates

`non_mf_groups_exist.tex`, proof of Theorem `thm:transport`.

Lines 543--549:

> If $(x_n)\in\mathcal C_2(V,L)$ and $\sup_n\hsnorm{x_n}\le c$, then
> $\operatorname{Ad}(V_n(\ell))x_n=x_n+o(1)$ in $\hsnorm{\,\cdot\,}$ for
> each $\ell\in F$, so
> \[ \limsup_n\hsnorm{P_nx_n-x_n}
>    \le\varepsilon c+\Bigl|\sum_{\ell\in F}a_\ell-1\Bigr|c \le2\varepsilon c, \]
> and $\varepsilon$ was arbitrary.

Lines 564--567:

> Since $uLu^{-1}\le L$, $U\widetilde\sigma(L)U^*\subseteq\widetilde\sigma(L)$,
> so $U^*PU\le P$ by Lemma~\ref{lem:kazhdan-projection-order}, and $U^*PU=P$
> by Lemma~\ref{lem:stable-finite}, since the two projections are unitarily
> equivalent.

Lines 570--580:

> For $(x_n)\in\mathcal C_2(V,L)$,
> \[ \hsnorm{P_n\operatorname{Ad}(V_n(u))^{\pm1}x_n
>      -\operatorname{Ad}(V_n(u))^{\pm1}x_n}
>    \le\opnorm{[P_n,\operatorname{Ad}(V_n(u))^{\pm1}]}\,\hsnorm{x_n}
>      +\hsnorm{P_nx_n-x_n}\longrightarrow0, \]
> so $\operatorname{Ad}(V(u))^{\pm1}x\in\mathcal C_2(V,L)$ by the
> displayed equivalence.

The objects are the corpus ones:
* `B : OpAlmostRepresentation G` is `(V_n)`;
* `sigmaB B` is `σ̃` and `sqCorona B` is `𝓑`;
* `f : C*_max(L) → 𝓑` sends `u_ℓ` to `σ̃(ℓ)`, and `f KD.projection` is `P`;
* `Pseq` is a lift `(P_n)` of `P`;
* `adMatrix (B.model n) (B.map n g)` is `Ad(V_n(g))`, and `applyOp` is its
  action on matrices;
* `printedCTwo B L` is `𝒞₂(V,L)`.

Proof route.
* 543--549.
  * The trivial character gives `|Σ a_ℓ − 1| < ε`.
  * `limsup_norm_sub_combSeq_lt` gives `‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ < ε`
    eventually.
  * `Ad(V_n(ℓ))x_n − x_n → 0` is the definition of `𝒞₂`.
  * The splitting
    `P_nx_n − x_n = (P_n − Σ a_ℓ Ad)x_n + Σ a_ℓ(Ad x_n − x_n) + (Σ a_ℓ − 1)x_n`
    bounds `‖P_nx_n − x_n‖₂` eventually by `εc + |Σ a_ℓ − 1|c + δ` for every
    `δ > 0`. This bounds the limsup.
* 564--567.
  * `u L u⁻¹ ≤ L` gives the compression of `σ̃(L)` (`compresses_coe`).
  * `commute_sigmaB_projection` gives `UP = PU`, which the corpus proves by
    the order lemma and the stable-finiteness comparison. Hence `U*PU = P`,
    and in particular `U*PU ≤ P`, i.e. `P (U*PU) = U*PU`.
* 570--580.
  * The estimate splits `P_n M x_n − M x_n = [P_n, M]x_n + M(P_nx_n − x_n)`,
    with `M` isometric in `‖·‖₂`.
  * The commutators tend to `0` (`tendsto_norm_commutator`, and its adjoint
    for `M = Ad(V_n(u)*)`), and `‖x_n‖₂` is bounded.
  * `tendsto_hsNorm_applyOp_projection_sub` gives `‖P_nx_n − x_n‖₂ → 0`.
  * Membership of `Ad(V(u))^{±1}x` in `𝒞₂` is the transport theorem
    `manuscriptPrintedTransportHS`, read at `x` and at its preimage.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditCompress1

open Filter Matrix Topology
open GroupApproximation.MaximalCStarKazhdanProjection
open GroupApproximation.KazhdanAsymptoticCommutant GroupApproximation.KazhdanCornerMatrices
open GroupApproximation.Manuscript.OneSidedMFRadical
open GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtAdMatrix
open GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction
open GroupApproximation.Manuscript.OneSidedMFRadical.TransportKazhdanProjection
open GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCommutation
open GroupApproximation.Manuscript.OneSidedMFRadical.TransportProjectionCharacterization
open GroupApproximation.Manuscript.OneSidedMFRadical.TransportPrintedCommutant
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The closing estimate for one coordinatewise operator `M` that is isometric
in `‖·‖₂`:
`‖P_n M x_n − M x_n‖₂ ≤ ‖[P_n, M]‖ ‖x_n‖₂ + ‖P_nx_n − x_n‖₂`. If the
commutators tend to `0`, `‖x_n‖₂ ≤ C`, and `‖P_nx_n − x_n‖₂ → 0`, then both
sides tend to `0`. -/
theorem closingEstimate_of {G : Type} [Group G] (B : OpAlmostRepresentation G)
    (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n)))
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
    (∀ n, hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (M n) (x n))
          - applyOp (B.model n) (M n) (x n))
      ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) ∧
    Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0) ∧
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
            (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
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
              (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n) :=
      hsNorm_applyOp_le (B.model n) hcard _ _
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
  have hbound2 : ∀ n, ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
      ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖ * C :=
    fun n ↦ mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
  have hlimC : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖ * C) atTop (nhds 0) := by
    simpa using hcomm.mul_const C
  have hprod : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n * M n
        - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
          (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n))
      atTop (nhds 0) :=
    squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (hsNorm_nonneg _ _))
      hbound2 hlimC
  have hrhs : Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * M n
          - M n * (Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0) := by
    simpa using hprod.add hx
  exact ⟨hbound, hrhs, squeeze_zero (fun n ↦ hsNorm_nonneg _ _) hbound hrhs⟩

#audit_axioms closingEstimate_of

/-- tex 570--580: for `(x_n) ∈ 𝒞₂(V,L)` and `u L u⁻¹ ≤ L`, with
`M_n = Ad(V_n(u))^{±1}`,
`‖P_n M_n x_n − M_n x_n‖₂ ≤ ‖[P_n, M_n]‖ ‖x_n‖₂ + ‖P_nx_n − x_n‖₂ → 0`.
The conclusion lists the inequality, the vanishing of the right side, and the
vanishing of the left side, first for `Ad(V_n(u))` and then for
`Ad(V_n(u))⁻¹ = Ad(V_n(u)*)`. -/
theorem manuscriptSentence_projectionAdjointClosingEstimate {G : Type} [Group G]
    (B : OpAlmostRepresentation G) [∀ n, Nonempty (B.model n)]
    (L : Subgroup G) (KD : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
    (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n)))
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPproj : ∀ n, IsOrthogonalProjectionMatrix
      ((Pseq : ∀ n, Matrix (sqModel (B.model n)) (sqModel (B.model n)) ℂ) n))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    {u : G} (hu : u ∈ compressionSet L)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) (hx : x ∈ printedCTwo B L) :
    ((∀ n, hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) (x n))
          - applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) (x n))
      ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * adMatrix (B.model n) (B.map n u)
          - adMatrix (B.model n) (B.map n u) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) ∧
    Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * adMatrix (B.model n) (B.map n u)
          - adMatrix (B.model n) (B.map n u) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0) ∧
    Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) (x n))
          - applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) (x n)))
      atTop (nhds 0)) ∧
    ((∀ n, hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n))
          - applyOp (B.model n) (adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n))
      ≤ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)
          - adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) ∧
    Tendsto (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n * adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)
          - adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
            (Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n‖ * hsNorm (B.model n) (x n)
        + hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop (nhds 0) ∧
    Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n)
            (applyOp (B.model n) (adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n))
          - applyOp (B.model n) (adMatrix (B.model n)
              ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) (x n)))
      atTop (nhds 0)) := by
  obtain ⟨C, hC⟩ := hx.1
  have hxP := tendsto_hsNorm_applyOp_projection_sub B L KD f Pseq hf hPmk x hx
  have hisoA : ∀ (n : ℕ) (a : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n)
          (applyOp (B.model n) (adMatrix (B.model n) (B.map n u)) a)
        = hsNorm (B.model n) a :=
    fun n a ↦ TransportPrintedRoute.hsNorm_applyOp_adMatrix_unitary (B.model n)
      (B.map n u).2 a
  have hisoB : ∀ (n : ℕ) (a : Matrix (B.model n) (B.model n) ℂ),
      hsNorm (B.model n)
          (applyOp (B.model n) (adMatrix (B.model n)
            ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ)) a)
        = hsNorm (B.model n) a :=
    fun n a ↦ TransportPrintedRoute.hsNorm_applyOp_adMatrix_unitary (B.model n)
      (GroupApproximation.conjTranspose_mem_unitaryGroup (B.map n u).2) a
  have hcommA := TransportPrintedRoute.tendsto_norm_commutator B L KD f Pseq hf
    hPmk hu
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
  exact ⟨closingEstimate_of B Pseq (fun n ↦ adMatrix (B.model n) (B.map n u))
      hisoA hcommA x hC hxP,
    closingEstimate_of B Pseq (fun n ↦ adMatrix (B.model n)
        ((B.map n u : Matrix (B.model n) (B.model n) ℂ)ᴴ))
      hisoB hcommB x hC hxP⟩

#audit_axioms manuscriptSentence_projectionAdjointClosingEstimate

/-- tex 543--549: let `F ⊆ L` and scalars `a_ℓ` satisfy `‖Σ a_ℓ u_ℓ − e_L‖ < ε`.
Let `(x_n) ∈ 𝒞₂(V,L)` with `sup_n ‖x_n‖₂ ≤ c`. Then:
* `Ad(V_n(ℓ))x_n = x_n + o(1)` in `‖·‖₂` for each `ℓ ∈ F`;
* `limsup_n ‖P_nx_n − x_n‖₂ ≤ εc + |Σ a_ℓ − 1| c`;
* `εc + |Σ a_ℓ − 1| c ≤ 2εc`. -/
theorem manuscriptSentence_projectionDefectLimsupBound {G : Type} [Group G]
    (B : OpAlmostRepresentation G) [∀ n, Nonempty (B.model n)]
    (L : Subgroup G) (KD : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
    (Pseq : BoundedMatrixSequence (fun n ↦ sqModel (B.model n)))
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    (hPmk : normMatrixCStarCoronaMk (fun n ↦ sqModel (B.model n)) Pseq
      = f KD.projection)
    (F : Finset ↥L) (alpha : ↥L → ℂ) {eps : ℝ}
    (hclose : ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator ↥L s)
      - KD.projection‖ < eps)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) (hx : x ∈ printedCTwo B L)
    {c : ℝ} (hc : ∀ n, hsNorm (B.model n) (x n) ≤ c) :
    (∀ s ∈ F, Tendsto (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n) (adMatrix (B.model n)
          (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0)) ∧
    Filter.limsup (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)) atTop
      ≤ eps * c + ‖(∑ s ∈ F, alpha s) - 1‖ * c ∧
    eps * c + ‖(∑ s ∈ F, alpha s) - 1‖ * c ≤ 2 * eps * c := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (hsNorm_nonneg (B.model 0) (x 0)) (hc 0)
  have heps0 : (0 : ℝ) < eps := lt_of_le_of_lt (norm_nonneg _) hclose
  -- the trivial character gives `|Σ a_ℓ − 1| < ε`
  have hchi : maximalGroupCStarTrivialCharacter ↥L
      ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator ↥L s) - KD.projection)
      = (∑ s ∈ F, alpha s) - 1 := by
    rw [map_sub, maximalGroupCStarTrivialCharacter_kazhdanProjection KD, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, maximalGroupCStarTrivialCharacter_generator, smul_eq_mul,
      mul_one]
  have hchar : ‖(∑ s ∈ F, alpha s) - 1‖ < eps := by
    rw [← hchi]
    exact lt_of_le_of_lt
      (NonUnitalStarAlgHom.norm_apply_le (maximalGroupCStarTrivialCharacter ↥L) _)
      hclose
  -- eventually `‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ < ε`
  have hlim := limsup_norm_sub_combSeq_lt B.model B.map
    (fun g h ↦ tendsto_mul_defect B g h) L KD f Pseq hf hPmk F alpha hclose
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.cofinite
      (fun n ↦ ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n
          - ∑ s ∈ F, alpha s •
            adMatrix (B.model n) (B.map n (L.subtype s))‖) := by
    refine Filter.isBoundedUnder_of ⟨‖Pseq‖ + ∑ s ∈ F, ‖alpha s‖, fun n ↦ ?_⟩
    refine (norm_sub_le _ _).trans (add_le_add
      (boundedMatrixSequence_coord_norm_le (fun n ↦ sqModel (B.model n))
        Pseq n) ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
    have h1 : ‖adMatrix (B.model n) (B.map n (L.subtype s))‖ = 1 :=
      CStarRing.norm_of_mem_unitary
        (adMatrix_mem_unitary (B.model n) (B.map n (L.subtype s)).2)
    exact le_of_eq (by rw [norm_smul, h1, mul_one])
  have hev1 : ∀ᶠ n in atTop, ‖(Pseq : ∀ n, Matrix (sqModel (B.model n))
        (sqModel (B.model n)) ℂ) n
      - ∑ s ∈ F, alpha s • adMatrix (B.model n) (B.map n (L.subtype s))‖
      < eps := by
    have h := Filter.eventually_lt_of_limsup_lt hlim hbdd
    rwa [Nat.cofinite_eq_atTop] at h
  -- `Ad(V_n(ℓ))x_n − x_n → 0` for every `ℓ ∈ L`
  have hAd : ∀ s : ↥L, Tendsto (fun n ↦ hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
    intro s
    have h := ((isHSAsymptoticallyCentral_iff_adjointSequence B L x).mp hx.2)
      (L.subtype s) s.2
    refine h.congr fun n ↦ ?_
    rw [applyOp_adMatrix_map B (L.subtype s) n (x n)]
    rfl
  have hone : ∀ s : ↥L, Tendsto (fun n ↦ ‖alpha s‖ * hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
    intro s
    simpa using (hAd s).const_mul ‖alpha s‖
  have hmid : Tendsto (fun n ↦ ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
      (applyOp (B.model n) (adMatrix (B.model n)
        (B.map n (L.subtype s))) (x n) - x n)) atTop (nhds 0) := by
    have h := tendsto_finsetSum F fun s (_ : s ∈ F) ↦ hone s
    simpa using h
  refine ⟨fun s _ ↦ hAd s, ?_, ?_⟩
  · refine le_of_forall_pos_lt_add fun δ hδ ↦ ?_
    have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
    have hev2 : ∀ᶠ n in atTop, ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
        (applyOp (B.model n) (adMatrix (B.model n)
          (B.map n (L.subtype s))) (x n) - x n) < δ / 2 := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hmid) (δ / 2) hδ2
      filter_upwards [eventually_ge_atTop N] with n hn
      have h2 := hN n hn
      rw [Real.dist_eq, sub_zero] at h2
      exact lt_of_abs_lt h2
    have hevb : ∀ᶠ n in atTop, hsNorm (B.model n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)
        ≤ eps * c + ‖(∑ s ∈ F, alpha s) - 1‖ * c + δ / 2 := by
      filter_upwards [hev1, hev2] with n h1 h2
      have hcard : 0 < Fintype.card (B.model n) := B.modelNonempty n
      have e1 : applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
              - ∑ s ∈ F, alpha s •
                adMatrix (B.model n) (B.map n (L.subtype s))) (x n)
          = applyOp (B.model n)
              ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n) (x n)
            - ∑ s ∈ F, alpha s • applyOp (B.model n)
                (adMatrix (B.model n) (B.map n (L.subtype s))) (x n) := by
        rw [applyOp_sub, applyOp_sum]
        congr 1
        exact Finset.sum_congr rfl fun s _ ↦ applyOp_smul _ _ _ _
      have e2 : (∑ s ∈ F, alpha s •
            (applyOp (B.model n) (adMatrix (B.model n)
              (B.map n (L.subtype s))) (x n) - x n))
          = (∑ s ∈ F, alpha s • applyOp (B.model n)
              (adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
            - (∑ s ∈ F, alpha s) • x n := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ ↦ smul_sub _ _ _
      have hsplit : applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n
          = applyOp (B.model n)
              ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                  (sqModel (B.model n)) ℂ) n
                - ∑ s ∈ F, alpha s •
                  adMatrix (B.model n) (B.map n (L.subtype s))) (x n)
            + (∑ s ∈ F, alpha s •
                (applyOp (B.model n) (adMatrix (B.model n)
                  (B.map n (L.subtype s))) (x n) - x n))
            + ((∑ s ∈ F, alpha s) - 1) • x n := by
        rw [e1, e2, sub_smul, one_smul, sub_add_sub_cancel, sub_add_sub_cancel]
      have hb1 : hsNorm (B.model n) (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n
            - ∑ s ∈ F, alpha s •
              adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
          ≤ eps * c :=
        le_trans (hsNorm_applyOp_le (B.model n) hcard _ _)
          (mul_le_mul h1.le (hc n) (hsNorm_nonneg _ _) heps0.le)
      have hb2 : hsNorm (B.model n) (∑ s ∈ F, alpha s •
            (applyOp (B.model n) (adMatrix (B.model n)
              (B.map n (L.subtype s))) (x n) - x n))
          ≤ ∑ s ∈ F, ‖alpha s‖ * hsNorm (B.model n)
              (applyOp (B.model n) (adMatrix (B.model n)
                (B.map n (L.subtype s))) (x n) - x n) := by
        refine le_trans (hsNorm_sum_le (B.model n) hcard F _) ?_
        exact Finset.sum_le_sum fun s _ ↦
          le_of_eq (hsNorm_smul (B.model n) hcard _ _)
      have hb3 : hsNorm (B.model n) (((∑ s ∈ F, alpha s) - 1) • x n)
          ≤ ‖(∑ s ∈ F, alpha s) - 1‖ * c := by
        rw [hsNorm_smul (B.model n) hcard]
        exact mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)
      have htri : hsNorm (B.model n) (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
              (sqModel (B.model n)) ℂ) n) (x n) - x n)
          ≤ hsNorm (B.model n) (applyOp (B.model n)
              ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                  (sqModel (B.model n)) ℂ) n
                - ∑ s ∈ F, alpha s •
                  adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
            + hsNorm (B.model n) (∑ s ∈ F, alpha s •
                (applyOp (B.model n) (adMatrix (B.model n)
                  (B.map n (L.subtype s))) (x n) - x n))
            + hsNorm (B.model n) (((∑ s ∈ F, alpha s) - 1) • x n) := by
        rw [hsplit]
        refine le_trans (hsNorm_add_le (B.model n) hcard _ _) ?_
        have := hsNorm_add_le (B.model n) hcard
          (applyOp (B.model n)
            ((Pseq : ∀ n, Matrix (sqModel (B.model n))
                (sqModel (B.model n)) ℂ) n
              - ∑ s ∈ F, alpha s •
                adMatrix (B.model n) (B.map n (L.subtype s))) (x n))
          (∑ s ∈ F, alpha s •
            (applyOp (B.model n) (adMatrix (B.model n)
              (B.map n (L.subtype s))) (x n) - x n))
        linarith
      linarith [htri, hb1, hb2, hb3, h2]
    have hcob : Filter.IsCoboundedUnder (· ≤ ·) atTop (fun n ↦ hsNorm (B.model n)
        (applyOp (B.model n)
          ((Pseq : ∀ n, Matrix (sqModel (B.model n))
            (sqModel (B.model n)) ℂ) n) (x n) - x n)) :=
      Filter.isCoboundedUnder_le_of_le atTop fun n ↦ hsNorm_nonneg _ _
    have hle := Filter.limsup_le_of_le hcob hevb
    linarith
  · have h := mul_le_mul_of_nonneg_right hchar.le hc0
    linarith

#audit_axioms manuscriptSentence_projectionDefectLimsupBound

/-- tex 564--567: put `U = σ̃(u)` with `u L u⁻¹ ≤ L`. Then:
* `U σ̃(L) U* ⊆ σ̃(L)`;
* `U*PU ≤ P`, written `P (U*PU) = U*PU`;
* `U*PU = P`. -/
theorem manuscriptSentence_compressorConjugateProjectionEqual {G : Type}
    [Group G] (B : OpAlmostRepresentation G) [∀ n, Nonempty (B.model n)]
    (L : Subgroup G) (KD : KazhdanData ↥L)
    (f : MaximalGroupCStar ↥L →⋆ₐ[ℂ] sqCorona B)
    (hf : ∀ s : ↥L, f (maximalGroupCStarGenerator ↥L s)
      = ((sigmaB B (L.subtype s) : unitary (sqCorona B)) : sqCorona B))
    {u : G} (hu : u ∈ compressionSet L) :
    (∀ s : ↥L, ∃ t : ↥L,
      ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
          (((sigmaB B).comp L.subtype s : unitary (sqCorona B)) : sqCorona B) *
          star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
        = (((sigmaB B).comp L.subtype t : unitary (sqCorona B)) :
            sqCorona B)) ∧
    f KD.projection *
        (star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
          f KD.projection * ((sigmaB B u : unitary (sqCorona B)) : sqCorona B))
      = star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
          f KD.projection * ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) ∧
    star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
        f KD.projection * ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
      = f KD.projection := by
  have hU : star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
      ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) = 1 :=
    Unitary.star_mul_self_of_mem (sigmaB B u).2
  have hcomm := commute_sigmaB_projection B L KD f hf hu
  have heq : star ((sigmaB B u : unitary (sqCorona B)) : sqCorona B) *
        f KD.projection * ((sigmaB B u : unitary (sqCorona B)) : sqCorona B)
      = f KD.projection := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, hU, one_mul]
  refine ⟨?_, ?_, heq⟩
  · refine compresses_coe ((sigmaB B).comp L.subtype) (sigmaB B u) ?_
    intro s
    refine ⟨⟨u * (s : G) * u⁻¹, hu (s : G) s.2⟩, ?_⟩
    show sigmaB B u * sigmaB B (s : G) * (sigmaB B u)⁻¹
      = sigmaB B (u * (s : G) * u⁻¹)
    rw [map_mul, map_mul, map_inv]
  · rw [heq]
    exact image_mul_image KD f

#audit_axioms manuscriptSentence_compressorConjugateProjectionEqual

/-- tex 579--580: if `L` has property (T), `u L u⁻¹ ≤ L`, and
`x ∈ 𝒞₂(V,L)`, then `Ad(V(u)) x ∈ 𝒞₂(V,L)` and `Ad(V(u))⁻¹ x ∈ 𝒞₂(V,L)`. -/
theorem manuscriptSentence_adjointPlusMinusMemPrintedCTwo (G : Type) [Group G]
    (L : Subgroup G) (hT : HasKazhdanPropertyT.{0, 0} L)
    (B : OpAlmostRepresentation G) {u : G} (hu : u ∈ compressionSet L)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) (hx : x ∈ printedCTwo B L) :
    adjointSequence B u x ∈ printedCTwo B L ∧
      coadjointSequence B u x ∈ printedCTwo B L := by
  have himg := TransportPrintedRoute.manuscriptPrintedTransportHS G L hT B u hu
  refine ⟨?_, ?_⟩
  · have h := Set.mem_image_of_mem (adjointSequence B u) hx
    rwa [himg] at h
  · have hx' : x ∈ adjointSequence B u '' printedCTwo B L := by
      rw [himg]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [← hyx,
      GroupApproximation.Manuscript.OneSidedMFRadical.coadjointSequence_adjointSequence]
    exact hy

#audit_axioms manuscriptSentence_adjointPlusMinusMemPrintedCTwo

end

end GroupApproximation.Manuscript.NonMF.AuditCompress1
