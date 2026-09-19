import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Sofic.OmegaWeightedAmbient
import GroupApproximation.Sofic.KazhdanTransportAnyUniverse

/-!
# `thm:kazhdan-transport` in its badged shape, through `∏_ω B(K_n)`

Ledger rows `UF.01` and `UF.03` record the sharpest divergence in the
development: the algebra realizing the printed `B_ω` in the proof the manuscript
badges is the **cofinite** norm corona `∏_∞ B(K_n)`, not the printed
`∏_ω B(K_n)`.  The substitution costs the transport theorem nothing — `ω ≤
cofinite`, so the cofinite-null ideal sits inside the `ω`-null one and the
identity `Q = P` descends — but it is not a construction of `∏_ω B(K_n)`, and
the ledger says so.

`Sofic/OmegaWeightedAmbient.lean` closes that.  It builds the ambient over the
genuine `B_ω = ∏_ω B(K_n)` — the quotient of the bounded sequences by the
`ω`-null ideal, not by the `c₀` ideal — and `omega_route_kazhdan_transport`
derives the conclusion of `thm:kazhdan-transport` through it, with the ambient
constructed rather than assumed.  Nothing cited it.  This file states that
result in the shape the manuscript badge is written in, so the printed route and
the printed statement meet.

## The two shape changes

Neither is mathematical.

*Coordinates.*  `omega_route_kazhdan_transport` is stated over an arbitrary
family `Y : ℕ → FiniteModel`; the badge is stated over `naturalFiniteModel (d n)`,
which is such a family.  The instantiation is the only step.

*Convergence.*  The badge writes the vanishing as
`∀ ε > 0, ∃ N, ∀ n ≥ N, √(hsNormSq …) ≤ ε` and the `ω` route as
`Tendsto (fun n ↦ hsNormSq …) atTop (𝓝 0)`.  These are the same statement for a
nonnegative sequence, and `tendsto_iff_sqrt_le` below is the translation, used in
both directions.

## What this does not change

The badged `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` still runs
through the cofinite corona, and is left alone deliberately: rewiring it would
leave the corpus with one theorem wearing two proofs and no way to tell from a
name which ambient a consumer traversed, which is the defect class this audit
exists to catch.  The two are interchangeable — identical statement, identical
hypotheses, different ambient — and a consumer picks its route by picking its
name, exactly as `Sofic/LiteralRouteTransport.lean` does for the finite-stage
engine.

## The universes

`Sofic/OmegaWeightedAmbient.lean` carries the ambient group at an arbitrary
universe, and so does this file.  The Kazhdan source is a different matter: the
`ω`-route chain consumes property `(T)` in its `Type 0` real form, and freeing
it by generalizing that chain would mean re-elaborating the whole compression
bundle.  It does not need to be freed there, for the same reason
`Sofic/KazhdanTransportAnyUniverse.lean` records for the cofinite route:
**property `(T)` implies countability**, so a Kazhdan source at any universe has
a `Type 0` model that still has property `(T)`, and the theorem transfers along
the isomorphism.  `manuscriptKazhdanTransport_omegaRoute_anyUniverse` below is
that closure: both groups at arbitrary universes, no hypothesis the print does
not state, and the proof running through `B_ω = ∏_ω B(K_n)`.  It is the single
declaration the `INT.03` ledger row asked for — the any-universe statement and
the printed §3 route no longer live in different theorems.
-/

namespace GroupApproximation
namespace OmegaRouteManuscriptTransport

open Filter Matrix Topology
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- For a nonnegative sequence, `√aₙ` is eventually below every positive `ε`
exactly when `aₙ → 0`.  The badge writes the first, the `ω` route the second. -/
theorem tendsto_iff_sqrt_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    Tendsto a atTop (𝓝 0) ↔ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, Real.sqrt (a n) ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hlt := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)] at hlt
    calc Real.sqrt (a n) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hlt.le
      _ = ε := Real.sqrt_sq hε.le
  · intro h
    refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := h (Real.sqrt (ε / 2)) (Real.sqrt_pos.2 (by positivity))
    refine ⟨N, fun n hn ↦ ?_⟩
    have hsq : a n ≤ ε / 2 := by
      have h1 : Real.sqrt (a n) ^ 2 ≤ Real.sqrt (ε / 2) ^ 2 := by
        have := hN n hn
        nlinarith [Real.sqrt_nonneg (a n)]
      rwa [Real.sq_sqrt (ha n), Real.sq_sqrt (by positivity : (0:ℝ) ≤ ε / 2)] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (ha n)]
    linarith

universe u v w

variable {H : Type u} [Group H]

/-- **`thm:kazhdan-transport`, badged shape, printed ambient.**

Character for character the statement of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, with the ambient group
at an arbitrary universe and the Kazhdan source at `Type 0`, and proved through
`B_ω = ∏_ω B(K_n)` acting on `K_ω` rather than through the cofinite corona.
The ambient is not a hypothesis: it is built from the theorem's own data by
`OmegaWeightedAmbient.omegaWeightedAmbient`.  The source universe is freed in
`manuscriptKazhdanTransport_omegaRoute_anyUniverse` below. -/
theorem manuscriptKazhdanTransport_omegaRoute
    {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyT.{0, 0} Γ)
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
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) := by
  classical
  set Y : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n) with hY0
  have hY : ∀ n, 0 < Fintype.card (Y n) := by
    intro n
    simpa [hY0] using hd n
  haveI : ∀ n, Nonempty (Y n) := fun n ↦ Fintype.card_pos_iff.mp (hY n)
  -- The operator-norm bound the manuscript states gives the Hilbert--Schmidt
  -- mass bound the `ω` route asks for; this is the first printed inequality
  -- `‖A‖₂ ≤ ‖A‖`, in squared form.
  obtain ⟨M, hM0, hM⟩ := hbound
  have hmass : ∀ n, hsNormSq (Y n) (x n) ≤ M * M := by
    intro n
    calc hsNormSq (Y n) (x n) ≤ ‖x n‖ * ‖x n‖ :=
          hsNormSq_le_mul_self_l2_opNorm (Y n) (hY n) (x n)
      _ ≤ M * M := mul_le_mul (hM n) (hM n) (norm_nonneg _) hM0
  have hcomm : ∀ γ : Γ, Tendsto
      (fun n ↦ hsNormSq (Y n)
        (x n * (U n (iota γ) : Matrix (Y n) (Y n) ℂ) -
          (U n (iota γ) : Matrix (Y n) (Y n) ℂ) * x n))
      atTop (𝓝 0) := by
    intro γ
    exact (tendsto_iff_sqrt_le (fun n ↦ hsNormSq_nonneg (Y n) _)).2 (hx γ)
  intro γ
  refine (tendsto_iff_sqrt_le (fun n ↦ hsNormSq_nonneg (Y n) _)).1 ?_
  exact OmegaWeightedAmbient.omega_route_kazhdan_transport Y hY U hU hT iota s hs
    (M * M) x hmass hcomm γ

/-- **`thm:kazhdan-transport` with both groups at arbitrary universes, proved
through the printed ambient `B_ω = ∏_ω B(K_n)`.**

Statement for statement this is
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport_anyUniverse`: property
`(T)` for the source, a homomorphism into the ambient, a compressing element,
positive dimensions, an operator-norm asymptotic representation, a uniform
operator-norm bound on `x`, asymptotic commutation with the image of `Γ`, and
no countability hypothesis on either group.  What differs is the proof: the
route is the `ω`-ultraproduct one, with the ambient constructed from the
theorem's own data by `OmegaWeightedAmbient.omegaWeightedAmbient`, not the
cofinite corona.

The source is moved to its `Type 0` model exactly as the any-universe closure
of the cofinite route moves it: property `(T)` implies countability
(`countable_of_hasKazhdanPropertyTComplex`), the model still has property `(T)`
(`HasKazhdanPropertyTComplex.mulEquiv`), the textbook equivalence turns the
complex form into the real `Type 0` form the compression bundle consumes, and
the conclusion mentions only `U n s` and `U n (ι γ)`, so it pushes forward
along the isomorphism unchanged.

Every binder is after the colon, as the badged declarations have it: the
zero-input gate rejects a badged declaration with header binders. -/
theorem manuscriptKazhdanTransport_omegaRoute_anyUniverse :
    ∀ {Γ : Type w} {H : Type u} [Group Γ] [Group H]
      (_hT : HasKazhdanPropertyTComplex.{w, max w v} Γ)
      (iota : Γ →* H) (s : H)
      (_hs : ∀ γ : Γ, ∃ δ : Γ, s * iota γ * s⁻¹ = iota δ)
      (d : ℕ → ℕ) (_hd : ∀ n, 0 < d n)
      (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
      (_hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) -
          (U n g : Matrix (naturalFiniteModel (d n))
            (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
      (x : ∀ n, Matrix (naturalFiniteModel (d n)) (naturalFiniteModel (d n)) ℂ)
      (_hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
      (_hx : ∀ γ : Γ, NaturalHSCommutatorVanishing d U x (iota γ)),
    ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) := by
  intro Γ H _ _ hT iota s hs d hd U hU x hbound hx γ
  haveI : Countable Γ := countable_of_hasKazhdanPropertyTComplex.{w, v} hT
  obtain ⟨Γ₀, _, ⟨e⟩⟩ := Type0Transfer.exists_type0_model Γ
  have hT₀c : HasKazhdanPropertyTComplex.{0, max w v} Γ₀ := hT.mulEquiv e
  have hT₀ : HasKazhdanPropertyT.{0, 0} Γ₀ :=
    (hasKazhdanPropertyT_iff_textbook.{0, max w v}).mpr hT₀c
  have hpull : ∀ γ₀ : Γ₀, (iota.comp e.symm.toMonoidHom) γ₀ = iota (e.symm γ₀) :=
    fun γ₀ ↦ rfl
  have hs₀ : ∀ γ₀ : Γ₀, ∃ δ₀ : Γ₀,
      s * (iota.comp e.symm.toMonoidHom) γ₀ * s⁻¹
        = (iota.comp e.symm.toMonoidHom) δ₀ := by
    intro γ₀
    obtain ⟨δ, hδ⟩ := hs (e.symm γ₀)
    refine ⟨e δ, ?_⟩
    rw [hpull, hpull, e.symm_apply_apply]
    exact hδ
  have hx₀ : ∀ γ₀ : Γ₀,
      NaturalHSCommutatorVanishing d U x ((iota.comp e.symm.toMonoidHom) γ₀) :=
    fun γ₀ ↦ by rw [hpull]; exact hx (e.symm γ₀)
  have hconc := manuscriptKazhdanTransport_omegaRoute hT₀
    (iota.comp e.symm.toMonoidHom) s hs₀ d hd U hU x hbound hx₀ (e γ)
  rw [hpull, e.symm_apply_apply] at hconc
  exact hconc

end

end OmegaRouteManuscriptTransport
end GroupApproximation
