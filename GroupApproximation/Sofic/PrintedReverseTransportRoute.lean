import GroupApproximation.Analysis.PrintedReverseTransport
import GroupApproximation.Sofic.LiteralRouteTransport

/-!
# `cor:generaltransport`, both halves on the printed route

Proof-ledger row `ID.06`.  The printed proof of
`\begin{corollary}[one-sided conjugators preserve the commutant under
conjugation and inverse conjugation]` (`\label{cor:generaltransport}`) reads

> For a one-sided conjugator `s`, Theorem 3.1 gives the conclusion for
> `V_{g,n} x_n V_{g,n}^*`, and the equality `P = VPV^*` established in its proof
> gives `V^*PV = P`, hence `V^* Fix = Fix` and the conclusion for
> `V_{g,n}^* x_n V_{g,n}`.

The forward half is `KazhdanAsymptoticCommutant.transport_literal`, which row
`ID.05` closed.  The reverse half was `transport_star`, which reverses the
*approximate* leakage bound `one_sub_moved_mul_corner_vanishing` at the finite
stage -- a different argument in kind, as `ID.06` records.  The exact identity
the printed step turns on was formalized abstractly in
`Analysis/PrintedReverseTransport` and had no consumer.  This file is that
consumer.

## Where the printed step enters, and why it is only one line

`Sofic/UltraproductKazhdanTransport.lean` bundles manuscript steps KT.01--KT.09
as `UltraproductAdjointModel iota s d U ω`, and exactly two of its fields
mention the conjugator `s`: the absorption identities `P ≤ Q` for
`Q = V P V^*`, `V = π s`.  Its `kt_10_conjugate_eq` is the printed
`P = V P V^*`.

So `starModel` below is the printed sentence and nothing else: applying
`PrintedReverseTransport.star_conj_eq_of_conj_eq` to `kt_10_conjugate_eq` gives
`V^* P V = P` exactly, and since `π s⁻¹ = star (π s)` that says the *same
bundle* is an adjoint model for the conjugator `s⁻¹`.  Both absorption fields
then hold with no inequality left over, because `P` absorbs itself.

Everything downstream follows by *applying the existing printed theorem at
`s⁻¹`*.  No transport is reproved: `ultraproductKazhdanTransport` is invoked
once more, on the model the printed reverse step produced.  In particular the
reverse half is not an estimate, exactly as `ID.06` asks.

## The one bookkeeping step at the consumers

The printed conclusion is about `V^* x V`, and the ultraproduct route delivers
it about `U_n(s⁻¹) x_n U_n(s⁻¹)^*`.  For an operator-norm almost representation
these agree asymptotically -- `KazhdanCornerMatrices.map_inv_vanishing` is
`‖U_n(s⁻¹) - U_n(s)^*‖ → 0` -- and `transport_star_printed` performs that
exchange.  It is operator-norm bookkeeping of the same kind
`Sofic/LiteralRouteTransport.lean` already performs for the forward half's two
shape changes, and it introduces no estimate of the transport.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

universe u w

/-! ## The printed reverse step, in the adjoint model -/

namespace UltraproductAdjointModel

/-- **`P = VPV^* ⟹ V^*PV = P`, read as a model for the inverse conjugator.**

The manuscript's reverse step, at the place the manuscript makes it.  Only the
two absorption fields of `UltraproductAdjointModel` mention the conjugator, and
`PrintedReverseTransport.star_conj_eq_of_conj_eq` applied to
`kt_10_conjugate_eq` discharges both for `s⁻¹` at once: it gives
`π s⁻¹ * P * star (π s⁻¹) = P` on the nose, so the absorption identities reduce
to `P * P = P`.

This is why the reverse half costs no analysis.  The forward half spends
finiteness of `B_ω` to turn `P ≤ Q` into `Q = P` (KT.10); once that equality is
available, reversing it is star-ring algebra. -/
def starModel
    {Γ : Type} {H : Type*} [Group Γ] [Group H]
    {iota : Γ →* H} {s : H} {d : ℕ → ℕ}
    {U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ}
    {ω : Ultrafilter ℕ}
    (D : UltraproductAdjointModel iota s d U ω) :
    UltraproductAdjointModel iota s⁻¹ d U ω :=
  have hinv : D.pi s⁻¹ = star (D.pi s) := (D.pi_star s).symm
  have hkey : D.pi s⁻¹ * D.P * star (D.pi s⁻¹) = D.P := by
    rw [hinv, star_star]
    exact PrintedReverseTransport.star_conj_eq_of_conj_eq
      (D.star_pi_mul_pi s) D.kt_10_conjugate_eq
  { D with
    P_mul_conjugate := by rw [hkey]; exact D.P_mul_P
    conjugate_mul_P := by rw [hkey]; exact D.P_mul_P }

end UltraproductAdjointModel

/-! ## The reverse conclusion, up the printed chain -/

namespace KazhdanAsymptoticCommutant

open GroupApproximation.GeneralModelTransport

/-- **Reverse Kazhdan transport in the exact manuscript coordinates.**

`manuscriptKazhdanTransport` with the conjugator inverted in the conclusion and
nowhere else: the compression hypothesis is still about `s`, because that is
what builds the adjoint model, and the model for `s⁻¹` is produced from it by
the printed reverse step `UltraproductAdjointModel.starModel`.

The proof is one further application of `ultraproductKazhdanTransport`, so the
route is the printed §3 ultraproduct argument for both halves. -/
theorem manuscriptKazhdanTransportStar
    {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, NaturalHSCommutatorVanishing d U x (iota γ)) :
    ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s⁻¹ : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s⁻¹ : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) :=
  ultraproductKazhdanTransport iota s⁻¹ d hd U x hbound hx
    (fun ω hω ↦ (UltraproductModelConstruction.ultraproductAdjointModel
      (hasKazhdanPropertyT_iff_textbook.mpr hT) iota s hs d hd U hU ω hω).starModel)

end KazhdanAsymptoticCommutant

namespace GeneralModelTransport

open KazhdanAsymptoticCommutant MatrixReindexHS

/-- **Reverse Kazhdan transport over an arbitrary finite-model family.**

`generalModelKazhdanTransport` with the conjugator inverted in the conclusion.
The proof is that one, character for character, with
`manuscriptKazhdanTransportStar` in place of `manuscriptKazhdanTransport`: the
change of basis is indifferent to which group element is being conjugated
by. -/
theorem generalModelKazhdanTransportStar
    {Γ : Type} {H : Type u} [Group Γ] [Group H]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
    (Y : ℕ → FiniteModel) (hY : ∀ n, 0 < Fintype.card (Y n))
    (U : ∀ n, H → Matrix.unitaryGroup (Y n) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (Y n) (Y n) ℂ) -
        (U n g : Matrix (Y n) (Y n) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (Y n) (Y n) ℂ)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, GeneralHSCommutatorVanishing Y U x (iota γ)) :
    ∀ γ : Γ, GeneralHSCommutatorVanishing Y U (fun n ↦
      (U n s⁻¹ : Matrix (Y n) (Y n) ℂ) * x n *
        (U n s⁻¹ : Matrix (Y n) (Y n) ℂ)ᴴ) (iota γ) := by
  classical
  have hU' : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(naturalizeUnitary Y U n (g * h) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n g :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeUnitary Y U n h‖ ≤ ε := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := hU g h ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hrw : (naturalizeUnitary Y U n (g * h) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n g :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeUnitary Y U n h
        = naturalize Y n ((U n (g * h) : Matrix (Y n) (Y n) ℂ) -
            (U n g : Matrix (Y n) (Y n) ℂ) * U n h) := by
      simp only [map_sub, map_mul, coe_naturalizeUnitary]
    rw [hrw, norm_naturalize]
    exact hN n hn
  have hbound' : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖naturalizeSeq Y x n‖ ≤ M := by
    obtain ⟨M, hM0, hM⟩ := hbound
    refine ⟨M, hM0, fun n ↦ ?_⟩
    rw [naturalizeSeq_apply, norm_naturalize]
    exact hM n
  have hx' : ∀ γ : Γ, NaturalHSCommutatorVanishing
      (fun n ↦ Fintype.card (Y n)) (naturalizeUnitary Y U)
      (naturalizeSeq Y x) (iota γ) := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    show Real.sqrt (hsNormSq (naturalizedModel Y n)
      (naturalizeSeq Y x n *
          (naturalizeUnitary Y U n (iota γ) :
            Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n (iota γ) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeSeq Y x n)) ≤ ε
    have hrw : naturalizeSeq Y x n *
          (naturalizeUnitary Y U n (iota γ) :
            Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) -
        (naturalizeUnitary Y U n (iota γ) :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
          naturalizeSeq Y x n
        = naturalize Y n (x n * (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n) := by
      simp only [map_sub, map_mul, coe_naturalizeUnitary, naturalizeSeq_apply]
    rw [hrw, hsNormSq_naturalize]
    exact hN n hn
  have hmain := manuscriptKazhdanTransportStar hT iota s hs
    (fun n ↦ Fintype.card (Y n)) hY (naturalizeUnitary Y U) hU'
    (naturalizeSeq Y x) hbound' hx'
  intro γ ε hε
  obtain ⟨N, hN⟩ := hmain γ ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hstep := hN n hn
  have hPconj : (naturalizeUnitary Y U n s⁻¹ :
        Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ) *
        naturalizeSeq Y x n *
        (naturalizeUnitary Y U n s⁻¹ :
          Matrix (naturalizedModel Y n) (naturalizedModel Y n) ℂ)ᴴ
      = naturalize Y n ((U n s⁻¹ : Matrix (Y n) (Y n) ℂ) * x n *
          (U n s⁻¹ : Matrix (Y n) (Y n) ℂ)ᴴ) := by
    rw [naturalize_conj, coe_naturalizeUnitary, naturalizeSeq_apply]
  simp only [hPconj] at hstep
  simp only [naturalize_commutator Y U n (iota γ)
    ((U n s⁻¹ : Matrix (Y n) (Y n) ℂ) * x n *
      (U n s⁻¹ : Matrix (Y n) (Y n) ℂ)ᴴ)] at hstep
  have hstep' : Real.sqrt (hsNormSq (naturalizedModel Y n)
      (naturalize Y n ((U n s⁻¹ : Matrix (Y n) (Y n) ℂ) * x n *
          (U n s⁻¹ : Matrix (Y n) (Y n) ℂ)ᴴ *
            (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) *
            ((U n s⁻¹ : Matrix (Y n) (Y n) ℂ) * x n *
              (U n s⁻¹ : Matrix (Y n) (Y n) ℂ)ᴴ)))) ≤ ε := hstep
  rw [hsNormSq_naturalize] at hstep'
  exact hstep'

end GeneralModelTransport

/-! ## The consumers -/

namespace KazhdanAsymptoticCommutant

open GroupApproximation.GeneralModelTransport
open KazhdanCornerMatrices

/-- **Reverse transport at the inverse compressor, by the printed route.**

The conclusion is stated at `U_n(t⁻¹)`, which is what the ultraproduct route
delivers; `transport_star_printed` below moves it onto the printed `V^*`. -/
theorem transport_inv_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  have hT : HasKazhdanPropertyTComplex.{0, 0} Γ :=
    hasKazhdanPropertyT_iff_textbook.mp C.kazhdan
  have hY : ∀ n, 0 < Fintype.card (B.model n) := B.modelNonempty
  have hxgen : ∀ γ : Γ,
      GeneralHSCommutatorVanishing B.model B.map x (C.iota γ) := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
        ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
    have hdef : hsNormSq (B.model n)
        (x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        ≤ ε ^ 2 := hN n hn
    rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu (x n)]
      at hdef
    exact TransportShapeBridges.sqrt_hsNormSq_le_of_le_sq (B.model n) _
      hε.le hdef
  have hmain := generalModelKazhdanTransportStar hT C.iota C.t C.compresses
    B.model hY B.map B.asymptoticallyMultiplicative x hbound hxgen
  intro γ ε hε
  obtain ⟨N, hN⟩ := hmain γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
      ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
  have hcomm : Real.sqrt (hsNormSq (B.model n)
      (((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ)))
      ≤ Real.sqrt ε := hN n hn
  have hsq := TransportShapeBridges.hsNormSq_le_sq_of_sqrt_le (B.model n) _
    (Real.sqrt_nonneg ε) hcomm
  rw [Real.sq_sqrt hε.le] at hsq
  show hsNormSq (B.model n)
      (((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤ ε
  rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu _]
  exact hsq

/-- Two conjugations by asymptotically equal unitaries produce asymptotically
equal sequences, in operator norm.  This is the bookkeeping that turns the
ultraproduct route's `U_n(t⁻¹)` into the printed `V^*`. -/
theorem opNorm_conj_sub_conj_le {Y : FiniteModel}
    {A S x : Matrix Y Y ℂ} {M : ℝ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (hS : S ∈ Matrix.unitaryGroup Y ℂ)
    (hx : ‖x‖ ≤ M) :
    ‖A * x * Aᴴ - S * x * Sᴴ‖ ≤ 2 * M * ‖A - S‖ := by
  have hAle : ‖A‖ ≤ 1 := KazhdanCompressorCorner.norm_le_one_of_mem_unitary hA
  have hSle : ‖S‖ ≤ 1 := KazhdanCompressorCorner.norm_le_one_of_mem_unitary hS
  have hAHle : ‖Aᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact hAle
  have hAS : Aᴴ - Sᴴ = (A - S)ᴴ := (Matrix.conjTranspose_sub A S).symm
  have hnormAS : ‖(A - S)ᴴ‖ = ‖A - S‖ := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
  have hsplit : A * x * Aᴴ - S * x * Sᴴ
      = (A - S) * x * Aᴴ + S * x * (Aᴴ - Sᴴ) := by
    noncomm_ring
  have h1 : ‖(A - S) * x * Aᴴ‖ ≤ ‖A - S‖ * M := by
    calc ‖(A - S) * x * Aᴴ‖ ≤ ‖(A - S) * x‖ * ‖Aᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖(A - S) * x‖ * 1 :=
        mul_le_mul_of_nonneg_left hAHle (norm_nonneg _)
      _ = ‖(A - S) * x‖ := mul_one _
      _ ≤ ‖A - S‖ * ‖x‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖A - S‖ * M := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  have h2 : ‖S * x * (Aᴴ - Sᴴ)‖ ≤ M * ‖A - S‖ := by
    calc ‖S * x * (Aᴴ - Sᴴ)‖ ≤ ‖S * x‖ * ‖Aᴴ - Sᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ = ‖S * x‖ * ‖A - S‖ := by rw [hAS, hnormAS]
      _ ≤ (‖S‖ * ‖x‖) * ‖A - S‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ (1 * M) * ‖A - S‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hSle hx (norm_nonneg _) zero_le_one) (norm_nonneg _)
      _ = M * ‖A - S‖ := by rw [one_mul]
  calc ‖A * x * Aᴴ - S * x * Sᴴ‖
      = ‖(A - S) * x * Aᴴ + S * x * (Aᴴ - Sᴴ)‖ := by rw [hsplit]
    _ ≤ ‖(A - S) * x * Aᴴ‖ + ‖S * x * (Aᴴ - Sᴴ)‖ := norm_add_le _ _
    _ ≤ ‖A - S‖ * M + M * ‖A - S‖ := add_le_add h1 h2
    _ = 2 * M * ‖A - S‖ := by ring

/-- The conjugation-defect comparison: if `y` and `z` are close in normalized
Hilbert--Schmidt norm and `z` almost commutes with the unitary `V`, then so
does `y`.  The constants are the crude squared triangle inequality's, applied
twice. -/
theorem hsNormSq_conj_defect_transfer {Y : FiniteModel}
    (hY : 0 < Fintype.card Y) {V y z : Matrix Y Y ℂ}
    (hV : V ∈ Matrix.unitaryGroup Y ℂ) {ε : ℝ}
    (hyz : hsNormSq Y (y - z) ≤ ε / 12)
    (hzy : hsNormSq Y (z - y) ≤ ε / 12)
    (hz : hsNormSq Y (z - V * z * Vᴴ) ≤ ε / 8) :
    hsNormSq Y (y - V * y * Vᴴ) ≤ ε := by
  have hconjinv : hsNormSq Y (V * (z - y) * Vᴴ) = hsNormSq Y (z - y) :=
    hsNormSq_conjugate Y hV hY (z - y)
  have hdecomp : y - V * y * Vᴴ
      = (y - z) + ((z - V * z * Vᴴ) + V * (z - y) * Vᴴ) := by
    noncomm_ring
  have hstep1 := hsNormSq_add_le Y (y - z)
    ((z - V * z * Vᴴ) + V * (z - y) * Vᴴ)
  have hstep2 := hsNormSq_add_le Y (z - V * z * Vᴴ) (V * (z - y) * Vᴴ)
  rw [hconjinv] at hstep2
  rw [hdecomp]
  linarith

/-- **`cor:generaltransport`, the reverse half, by the printed route.**

Statement-identical to `KazhdanAsymptoticCommutant.transport_star`, proved from
the exact identity `P = VPV^* ⟹ V^*PV = P` rather than by reversing the
approximate leakage bound.  The two routes are interchangeable; a consumer
picks one by picking a name. -/
theorem transport_star_printed
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  obtain ⟨M, hM0, hMle⟩ := hbound
  have hinv := transport_inv_literal B C x hx ⟨M, hM0, hMle⟩
  intro γ ε hε
  have hMpos : (0 : ℝ) < 2 * M + 1 := by linarith
  have hε12 : (0 : ℝ) < ε / 12 := by linarith
  have hε8 : (0 : ℝ) < ε / 8 := by linarith
  have hroot : (0 : ℝ) ≤ Real.sqrt (ε / 12) := Real.sqrt_nonneg _
  obtain ⟨N₁, hN₁⟩ := hinv γ (ε / 8) hε8
  obtain ⟨N₂, hN₂⟩ := map_inv_vanishing B C.t
    (Real.sqrt (ε / 12) / (2 * M + 1))
    (div_pos (Real.sqrt_pos.mpr hε12) hMpos)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  have hcard : 0 < Fintype.card (B.model n) := B.modelNonempty n
  have hV : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
      ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
  have hAu : (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)
      ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n C.t⁻¹).2
  have hSu : (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ
      ∈ Matrix.unitaryGroup (B.model n) ℂ :=
    MarkedCompressionVectorChain.conjTranspose_mem_unitaryGroup (B.map n C.t).2
  -- the two conjugations differ by an operator-norm null amount
  have hdiffnorm : ‖(B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) -
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ‖ ≤
      Real.sqrt (ε / 12) / (2 * M + 1) := hN₂ n hn₂
  have habsorb : 2 * M * (Real.sqrt (ε / 12) / (2 * M + 1)) ≤
      Real.sqrt (ε / 12) := by
    have heq : 2 * M * (Real.sqrt (ε / 12) / (2 * M + 1))
        = 2 * M * Real.sqrt (ε / 12) / (2 * M + 1) := by ring
    rw [heq, div_le_iff₀ hMpos]
    nlinarith
  have hconj : ‖(B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
      (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ -
      ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ)‖ ≤
      Real.sqrt (ε / 12) := by
    refine le_trans (opNorm_conj_sub_conj_le hAu hSu (hMle n)) ?_
    exact le_trans
      (mul_le_mul_of_nonneg_left hdiffnorm (by linarith : (0 : ℝ) ≤ 2 * M))
      habsorb
  -- the same difference with the printed spelling of the second conjugation
  have hsimp : ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) :=
    Matrix.conjTranspose_conjTranspose _
  rw [hsimp] at hconj
  have hzy : hsNormSq (B.model n)
      ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) ≤ ε / 12 := by
    refine le_trans (hsNormSq_le_mul_self_l2_opNorm (B.model n) hcard _) ?_
    have hsq : Real.sqrt (ε / 12) * Real.sqrt (ε / 12) = ε / 12 :=
      Real.mul_self_sqrt hε12.le
    nlinarith [norm_nonneg
      ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ))]
  have hyz : hsNormSq (B.model n)
      ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤ ε / 12 := by
    have hneg : (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ
        = -((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
              (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ -
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
              (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
      abel
    rw [hneg, hsNormSq_neg]
    exact hzy
  have hzfix : hsNormSq (B.model n)
      ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤
      ε / 8 := hN₁ n hn₁
  exact hsNormSq_conj_defect_transfer hcard hV hyz hzy hzfix

/-- **`cor:generaltransport`, both halves on the printed route.**  The forward
half is `transport_literal` (row `ID.05`), the reverse half is
`transport_star_printed` (row `ID.06`); the printed corollary is exactly this
conjunction. -/
theorem transport_both_printed
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) :=
  ⟨transport_literal B C x hx hbound, transport_star_printed B C x hx hbound⟩

/-- **Every one-sided compressor transports both ways, on the printed
route.** -/
theorem compressionSet_transport_both_printed
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ gamma : Γ, HSSqVanishing B (fun n ↦
      x n - (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ) *
        x n * (B.map n (iota gamma) : Matrix (B.model n) (B.model n) ℂ)ᴴ))
    (hbound : IsUniformlyBounded B x)
    {s : E} (hs : s ∈ compressionSet iota.range) :
    IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B s x) := by
  let C := coreOfCompressor iota hkazhdan s hs
  have hxC : IsAsymptoticCommutant B C x := by
    change IsAsymptoticCommutantOf B iota x
    exact hx
  have htransport := transport_both_printed B C x hxC hbound
  change IsAsymptoticCommutantOf B C.iota (adjointSequence B C.t x) ∧
    IsAsymptoticCommutantOf B C.iota (coadjointSequence B C.t x) at htransport
  change IsAsymptoticCommutantOf B iota (adjointSequence B s x) ∧
    IsAsymptoticCommutantOf B iota (coadjointSequence B s x)
  exact htransport

theorem compressionSet_subset_asymptoticCommutantStabilizer_printed
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionSet iota.range ⊆ asymptoticCommutantStabilizer B iota := by
  intro s hs x hbound hx
  exact compressionSet_transport_both_printed B iota hkazhdan x hx hbound hs

theorem compressionGroup_le_asymptoticCommutantStabilizer_printed
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (iota : Γ →* E)
    (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionGroup iota.range ≤ asymptoticCommutantStabilizer B iota := by
  rw [compressionGroup, Subgroup.closure_le]
  exact compressionSet_subset_asymptoticCommutantStabilizer_printed B iota
    hkazhdan

/-- **`cor:generaltransport` on the printed route, in the form the manuscript
badge should cite.**  Same statement as
`compressionGroup_transport_both_literal`, with the reverse half no longer
routed through the approximate leakage bound. -/
theorem compressionGroup_transport_both_printed :
    ∀ {Γ₀ : Type} {E₀ : Type u} [Group Γ₀] [Group E₀]
    (B : OpAlmostRepresentation E₀) (iota : Γ₀ →* E₀)
    (_hkazhdan : HasKazhdanPropertyT.{0, 0} Γ₀)
    {g : E₀} (_hg : g ∈ compressionGroup iota.range)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (_hbound : IsUniformlyBounded B x)
    (_hx : IsAsymptoticCommutantOf B iota x),
    IsAsymptoticCommutantOf B iota (adjointSequence B g x) ∧
      IsAsymptoticCommutantOf B iota (coadjointSequence B g x) := by
  intro Γ₀ E₀ _ _ B iota hkazhdan g hg x hbound hx
  exact compressionGroup_le_asymptoticCommutantStabilizer_printed B iota
    hkazhdan hg x hbound hx

end KazhdanAsymptoticCommutant
end GroupApproximation
