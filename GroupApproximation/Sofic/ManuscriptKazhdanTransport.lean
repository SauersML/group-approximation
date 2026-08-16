import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.IntrinsicCompressionMFRadical
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# Exact manuscript form of Kazhdan transport

This file exposes the forward transport theorem with exactly the objects used
in the manuscript: natural matrix dimensions, raw unitary-valued
operator-norm almost representations, and normalized Hilbert--Schmidt
commutators.

`non_mf_groups_exist.tex` proves `\label{thm:kazhdan-transport}` **twice**,
and the remark `\label{rem:finite-stage}` advertises both proofs.  Exactly one
of the two is certified here:

* `finiteStageKazhdanTransport` -- **certified.**  The quantitative proof of
  `\section{The finite-stage transport proof}` (`\label{app:finite-stage}`),
  run at each single coordinate with an almost-fixed spectral subspace in
  place of the Kazhdan projection and the equal-rank reversal estimate in
  place of finiteness of `B_ω`.  This is the reusable
  `KazhdanAsymptoticCommutant.transport` in manuscript coordinates.
* `manuscriptKazhdanTransport_ultraproduct` -- **not certified.**  It replays
  the *printed* proof, the one set under the theorem in
  `\section{One-sided Kazhdan transport}` (`\label{sec:transport}`): the
  adjoint model, the norm ultraproduct `B_ω`, the Kazhdan projection,
  one-sided compression, and finiteness of `B_ω`.  But it is conditional on an
  `UltraproductAdjointModel`, and nothing in this repository constructs one,
  so it proves nothing about any actual ultraproduct yet.  Its machinery lives
  in `Sofic/UltraproductKazhdanTransport.lean`.

`manuscriptKazhdanTransport` is the theorem statement itself.  It is
unconditional, and it is established by the finite-stage route alone; the
printed ultraproduct proof remains unformalized until the interface acquires a
constructor.

TeX references here are by `\label` and sectioning command, never by line
number: the manuscript is under concurrent edit and offsets go stale within
minutes.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix
open scoped Matrix.Norms.L2Operator

universe w

variable {H : Type} [Group H]

/-- Convergence of a raw matrix commutator to zero in normalized
Hilbert--Schmidt norm, written in the natural coordinates `M_{d n}`. -/
def NaturalHSCommutatorVanishing
    (d : ℕ → ℕ)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (g : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    Real.sqrt (hsNormSq (naturalFiniteModel (d n))
      (x n * U n g - U n g * x n)) ≤ ε

/-- **The ultraproduct route to Kazhdan transport -- NOT YET CLOSED.**

This replays the proof set under `\label{thm:kazhdan-transport}` in
`non_mf_groups_exist.tex`, in the exact manuscript coordinates, but it is
**conditional on `ambient`, and nothing in this repository yet constructs an
`UltraproductAdjointModel`.**  So this declaration does *not* certify the
manuscript's printed proof, it must not carry a `\leanverified` badge, and it
must not be described as formalizing the ultraproduct argument.  It becomes a
certificate the moment a constructor for the interface exists; until then the
manuscript's printed proof is unformalized, and the theorem's unconditional
certificate is `manuscriptKazhdanTransport` below, by the finite-stage route.

The proof is by contradiction: the conclusion fails on an infinite set `I`, a
free ultrafilter `ω` containing `I` is fixed, and the ambient of manuscript
steps KT.01--KT.09 -- the adjoint model `K_n = L²(M_{d n}, tr_{d n})`, the
Hilbert-space ultraproduct `K_ω`, the norm ultraproduct `B_ω = ∏_ω B(K_n)`
with its faithful action, the homomorphism `π g = [Ad U_n g]_ω`, finiteness of
`B_ω`, and the Kazhdan projection `P` with `ran P = Fix` and `P ≤ V P V*` --
is supplied by `UltraproductAdjointModel`.  Steps KT.10 (finiteness reverses
the compression) and KT.11 (descent of the fixed vector) then close the
contradiction; see `Sofic/UltraproductKazhdanTransport.lean`.

Property `(T)` of `Γ` and the compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` are consumed by
the construction of the Kazhdan projection and by `Fix ⊆ V·Fix`, i.e. inside
KT.07--KT.09; operator-norm almost multiplicativity of `U` is consumed by
KT.01 and KT.05. -/
theorem manuscriptKazhdanTransport_ultraproduct
    {Γ : Type} [Group Γ]
    (_hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (_hs : ∀ γ : Γ, ∃ δ : Γ,
      s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (_hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, NaturalHSCommutatorVanishing d U x (iota γ))
    (ambient : ∀ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.cofinite →
      UltraproductAdjointModel iota s d U ω) :
    ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) :=
  ultraproductKazhdanTransport iota s d hd U x hbound hx ambient

/-- **Kazhdan transport, by the quantitative finite-stage proof.**
This is the proof of `\section{The finite-stage transport proof}`
(`\label{app:finite-stage}`), announced by the remark
`\label{rem:finite-stage}`: it runs at each
single coordinate `n`, with an explicit almost-fixed spectral subspace of the
averaged adjoint action in place of the Kazhdan projection and the equal-rank
reversal estimate in place of finiteness of the norm ultraproduct.  It gives
error bookkeeping in terms of `κ`, `|S|`, the uniform bound on `(x_n)`, and
the multiplicative defects of `U_n`; the ultrafilter proof gives no rate.

No lamp or centralizer datum is an input: the proof internally applies the
general compression theorem with the harmless root `1`. -/
theorem finiteStageKazhdanTransport
    {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ,
      s * iota γ * s⁻¹ = iota δ)
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
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) := by
  let B : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d n)
    modelNonempty := fun n ↦ by
      simpa using hd n
    map := U
    asymptoticallyMultiplicative := hU
  }
  let C : KazhdanCompressionCore Γ H := {
    iota := iota
    t := s
    c := 1
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hs
    comm_c γ := Commute.one_left (iota γ)
  }
  have hx_sq : IsAsymptoticCommutant B C x := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    let V : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ := U n (iota γ)
    have hV : V ∈ Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ :=
      (U n (iota γ)).2
    have hcomm := hN n hn
    have hcommSq : hsNormSq (naturalFiniteModel (d n))
        (x n * V - V * x n) ≤ ε := by
      calc
        hsNormSq (naturalFiniteModel (d n)) (x n * V - V * x n) =
            (Real.sqrt (hsNormSq (naturalFiniteModel (d n))
              (x n * V - V * x n))) ^ 2 :=
          (Real.sq_sqrt (hsNormSq_nonneg _ _)).symm
        _ ≤ (Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hcomm
        _ = ε := Real.sq_sqrt hε.le
    have hVVstar : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
    have hfactor : x n - V * x n * Vᴴ = (x n * V - V * x n) * Vᴴ := by
      noncomm_ring [hVVstar]
    change hsNormSq (naturalFiniteModel (d n)) (x n - V * x n * Vᴴ) ≤ ε
    rw [hfactor,
      hsNormSq_mul_right _
        (MarkedCompressionVectorChain.conjTranspose_mem_unitaryGroup hV)]
    exact hcommSq
  have hbound' : IsUniformlyBounded B x := hbound
  have hy_sq := transport B C x hx_sq hbound'
  intro γ ε hε
  obtain ⟨N, hN⟩ := hy_sq γ (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  let S : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := U n s
  let V : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := U n (iota γ)
  let y : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := S * x n * Sᴴ
  have hV : V ∈ Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ :=
    (U n (iota γ)).2
  have hVstarV : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hfactor : y * V - V * y = (y - V * y * Vᴴ) * V := by
    noncomm_ring [hVstarV]
  have hdisp : hsNormSq (naturalFiniteModel (d n))
      (y - V * y * Vᴴ) ≤ ε ^ 2 := by
    simpa [B, C, S, V, y] using hN n hn
  have hcommSq : hsNormSq (naturalFiniteModel (d n))
      (y * V - V * y) ≤ ε ^ 2 := by
    rw [hfactor, hsNormSq_mul_right _ hV]
    exact hdisp
  have hsqrt := Real.sqrt_le_sqrt hcommSq
  simpa [NaturalHSCommutatorVanishing, S, V, y,
    Real.sqrt_sq hε.le] using hsqrt

/-- **Kazhdan transport in the exact manuscript coordinates**
(`non_mf_groups_exist.tex`, `\label{thm:kazhdan-transport}`).

This is the theorem statement; the manuscript proves it twice and both proofs
are formalized.  The printed proof is `manuscriptKazhdanTransport_ultraproduct`
(the norm ultraproduct `B_ω`, the Kazhdan projection, one-sided compression,
and finiteness); the quantitative proof of `\label{app:finite-stage}`, which
the remark `\label{rem:finite-stage}` announces as the second proof, is
`finiteStageKazhdanTransport`.  The closed derivation below is the
finite-stage one, which needs no ultraproduct ambient. -/
theorem manuscriptKazhdanTransport :
    ∀ {Γ H : Type} [Group Γ] [Group H]
    (_hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (_hs : ∀ γ : Γ, ∃ δ : Γ,
      s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (_hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (_hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (_hx : ∀ γ : Γ, NaturalHSCommutatorVanishing d U x (iota γ)),
    ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) := by
  intro Γ H _ _ hT iota s hs d hd U hU x hbound hx
  exact finiteStageKazhdanTransport hT iota s hs d hd U hU x hbound hx

/-- **The intrinsic compression radical in the exact manuscript corona.**
For a countable ambient group, every finite normal subgroup of the intrinsic
compression--centralizer defect of a Kazhdan image lies in the literal
natural-dimension C-star-corona radical.  The second conjunct spells out the
equivalent kernel statement for every printed norm-matrix corona. -/
theorem manuscriptCompressionRadical :
    ∀ {Γ H : Type} [Group Γ] [Group H] [Countable H]
    (_hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H)
    (F : Subgroup H) [Finite F] [F.Normal]
    (_hF : F ≤ compressionCentralizerDefect iota.range),
    F ≤ manuscriptCoronaMFResidual H ∧
      ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : H →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          F ≤ rho.ker := by
  intro Γ H _ _ _ hT iota F _ _ hF
  have hnorm : F ≤ normMFResidual H :=
    finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect
      iota (hasKazhdanPropertyT_iff_textbook.mpr hT) F hF
  have hres : F ≤ manuscriptCoronaMFResidual H := by
    rw [manuscriptCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual]
    exact hnorm
  refine ⟨hres, ?_⟩
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho f hf
  exact MonoidHom.mem_ker.mpr
    ((mem_manuscriptCoronaMFResidual_iff.mp (hres hf)) d hd rho)

end KazhdanAsymptoticCommutant
end GroupApproximation
