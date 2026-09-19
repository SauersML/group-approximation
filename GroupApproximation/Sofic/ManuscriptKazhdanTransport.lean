import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.CompressionUniverseTransfer
import GroupApproximation.Sofic.IntrinsicCompressionMFRadical
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant
import GroupApproximation.Sofic.UltraproductKazhdanTransport
import GroupApproximation.Sofic.Type0Transfer
import GroupApproximation.Sofic.UltraproductModelConstructionAssembly

/-!
# Exact manuscript form of Kazhdan transport

This file exposes the forward transport theorem with exactly the objects used
in the manuscript: natural matrix dimensions, raw unitary-valued
operator-norm almost representations, and normalized Hilbert--Schmidt
commutators.

`non_mf_groups_exist.tex` prints one proof of `\ref{thm:kazhdan-transport}`;
this file certifies two, and it is worth being explicit about which is which:

* `manuscriptKazhdanTransport_ultraproduct` -- the *printed* proof, the one set
  under the theorem in `\section{One-sided conjugation in matrix models}`
  (`\ref{sec:transport}`): the adjoint model, the norm ultraproduct `B_ω`,
  the Kazhdan projection, one-sided compression, and finiteness of `B_ω`.  Its
  machinery lives in `Sofic/UltraproductKazhdanTransport.lean`, and the ambient
  it consumes is now built, from the theorem's own hypotheses and nothing else,
  by
  `Sofic/UltraproductModelConstructionAssembly.lean`
  (`UltraproductModelConstruction.ultraproductAdjointModel`).
* `finiteStageKazhdanTransport` -- a quantitative proof with no printed
  counterpart, run at each single coordinate with an almost-fixed spectral
  subspace in place of the Kazhdan projection and the equal-rank reversal
  estimate in place of finiteness of `B_ω`.  This is the reusable
  `KazhdanAsymptoticCommutant.transport` in manuscript coordinates.  Unlike the
  first, it gives an explicit rate.

**The manuscript used to print both.**  A remark announced the second proof and
an appendix carried it out; commit `3a45fa60` ("Editorial pass: rewrite orbit
collapse, cut what nothing uses") deleted both, because the rewritten collapse
step stopped consuming the finite-stage route and nothing else did.  Nothing
below changed with them -- the Lean proof was never a transcription of the
appendix -- but a reader looking for the printed second proof will not find
one, and no badge is owed on `finiteStageKazhdanTransport`.

`manuscriptKazhdanTransport` is the theorem statement itself, and it is the
declaration the manuscript badges.  It is unconditional and it is derived by
the **printed** route: its proof is one application of
`manuscriptKazhdanTransport_ultraproduct` with the ambient supplied by the
constructor.  The finite-stage route remains available, and reverting the
badged theorem to it is the single line
`exact finiteStageKazhdanTransport hT iota s hs d hd U hU x hbound hx`.

TeX references here are by `\label` and sectioning command, never by line
number: the manuscript is under concurrent edit and offsets go stale within
minutes.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix
open scoped Matrix.Norms.L2Operator

-- `w` is the representation-space universe of property `(T)`; `u` is the
-- universe of the ambient group in `manuscriptCompressionRadical`, whose
-- printed hypothesis is countability rather than smallness.
universe u w

variable {H : Type u} [Group H]

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

/-- **The ultraproduct route to Kazhdan transport.**

This replays the proof set under `\label{thm:kazhdan-transport}` in
`non_mf_groups_exist.tex`, in the exact manuscript coordinates.  It is stated
relative to `ambient`, the bundle of manuscript steps KT.01--KT.09, because
that is how the printed proof is organized: the ambient is an intermediate
*object* of the proof, not a hypothesis about the theorem.  The bundle is
constructed, from the theorem's own hypotheses and nothing else, by
`UltraproductModelConstruction.ultraproductAdjointModel`, and
`manuscriptKazhdanTransport` below discharges `ambient` with it.  So the
printed proof is formalized, and this declaration is what carries the theorem's
`\leanverified` badge through.

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
The manuscript printed this proof as an appendix until commit `3a45fa60` cut
it for want of a consumer, so it now has no printed counterpart: it runs at each
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
(`non_mf_groups_exist.tex`, `\ref{thm:kazhdan-transport}`).

This is the theorem statement.  The printed proof is
`manuscriptKazhdanTransport_ultraproduct`
(the norm ultraproduct `B_ω`, the Kazhdan projection, one-sided compression,
and finiteness); `finiteStageKazhdanTransport` is a second, quantitative proof
whose printed appendix was cut in `3a45fa60`.

The derivation below is the **printed** one.  The ambient of steps
KT.01--KT.09 that it consumes is built at every free ultrafilter by
`UltraproductModelConstruction.ultraproductAdjointModel`, whose inputs are
exactly the hypotheses displayed above: property `(T)` for `Γ`, the compression
`s ι(Γ) s⁻¹ ⊆ ι(Γ)`, positivity of the dimensions, and operator-norm asymptotic
multiplicativity of `U`.  Nothing further is assumed, so the theorem is
unconditional. -/
theorem manuscriptKazhdanTransport :
    ∀ {Γ : Type} {H : Type u} [Group Γ] [Group H]
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
  exact manuscriptKazhdanTransport_ultraproduct hT iota s hs d hd U hU x hbound
    hx (fun ω hω ↦ UltraproductModelConstruction.ultraproductAdjointModel
      (hasKazhdanPropertyT_iff_textbook.mpr hT) iota s hs d hd U hU ω hω)

/-- **The intrinsic compression radical in the exact manuscript corona.**
For a countable ambient group, every finite normal subgroup of the intrinsic
compression--centralizer defect of a Kazhdan image lies in the literal
natural-dimension C-star-corona radical.  The second conjunct spells out the
equivalent kernel statement for every printed norm-matrix corona.

The ambient group is at an arbitrary universe, as the printed hypothesis "let
`H` and `Γ` be countable groups" requires: countability is what makes a group a
`Type 0` group up to isomorphism, and the intrinsic radical theorem, which is
stated at `Type 0`, is reached by transporting along that isomorphism and
transporting the conclusion back.  The Kazhdan source `Γ` is still fixed at
`Type 0` by the spelling `HasKazhdanPropertyTComplex.{0, w}`; the printed
statement asks for it to be countable too, so that restriction remains. -/
theorem manuscriptCompressionRadical :
    ∀ {Γ : Type} {H : Type u} [Group Γ] [Group H] [Countable H]
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
  -- the `Type 0` model of the countable ambient group
  obtain ⟨H₀, _groupH₀, ⟨e⟩⟩ := Type0Transfer.exists_type0_model H
  haveI : Countable H₀ := Type0Transfer.countable_type0_model H e
  haveI : Finite (F.map e.toMonoidHom) :=
    CompressionUniverseTransfer.map_finite e F
  haveI : (F.map e.toMonoidHom).Normal :=
    CompressionUniverseTransfer.map_normal e F
  -- the defect hypothesis transports
  have hF₀ : F.map e.toMonoidHom ≤
      compressionCentralizerDefect (e.toMonoidHom.comp iota).range := by
    rw [MonoidHom.range_comp e.toMonoidHom iota]
    exact (Subgroup.map_mono hF).trans
      (CompressionUniverseTransfer.compressionCentralizerDefect_map_le e
        iota.range)
  -- the intrinsic radical theorem, at `Type 0`
  have hnorm₀ : F.map e.toMonoidHom ≤ normMFResidual H₀ :=
    finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect
      (e.toMonoidHom.comp iota) (hasKazhdanPropertyT_iff_textbook.mpr hT)
      (F.map e.toMonoidHom) hF₀
  have hres₀ : F.map e.toMonoidHom ≤ manuscriptCoronaMFResidual H₀ := by
    rw [manuscriptCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual]
    exact hnorm₀
  -- and the conclusion transports back, by functoriality of the radical
  have hres : F ≤ manuscriptCoronaMFResidual H := by
    intro f hf
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    have h₀ : e f ∈ actualCoronaMFResidual H₀ := by
      have hmem := hres₀ (CompressionUniverseTransfer.mem_map_of_mem e hf)
      rwa [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hmem
    have hpull : f ∈ (actualCoronaMFResidual H₀).map e.symm.toMonoidHom :=
      ⟨e f, h₀, by simp⟩
    exact map_actualCoronaMFResidual_le e.symm.toMonoidHom hpull
  refine ⟨hres, ?_⟩
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho f hf
  exact MonoidHom.mem_ker.mpr
    ((mem_manuscriptCoronaMFResidual_iff.mp (hres hf)) d hd rho)

end KazhdanAsymptoticCommutant
end GroupApproximation
