import GroupApproximation.Sofic.MarkedCompressionRootCapture
import GroupApproximation.Sofic.UltraproductKazhdanTransport

/-!
# INT.03 and INT.04: the rigidity claims through the printed transport

The introduction's rigidity paragraph (`p:abstract-mechanism`) says

> rigidity: if `t Γ t⁻¹ ⊆ Γ` then conjugation by `t` preserves the
> Hilbert--Schmidt asymptotic commutant of `Γ`,

and then, in `E`, that this forces the commutator `u` to converge to `1` in
normalized Hilbert--Schmidt norm.  The proof ledger records both rows as routed
through the **finite-stage** proof of `\label{app:finite-stage}`: `INT.03` reads
"the Lean route is Appendix B, not the printed §3 ultraproduct proof", and
`INT.04` reads "route via Appendix B".

That is accurate.  `LiteralNonMFEndpoint.kazhdanPinning` unfolds to
`KazhdanCompressionCore.compressionDefects_hsTrivial`, which unfolds to
`KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing`, and the *only*
step of that chain which is transport rather than operator-norm bookkeeping is

  `KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`,

proved with an almost-fixed spectral corner, `root_capture_vanishing` and the
reversal estimate -- Appendix B, with explicit constants `ε/6`, `ε/48` and
`θ = (c₀+1)/2`.  Meanwhile `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`,
which *is* derived by the printed §3 ultraproduct proof
(`ultraproductKazhdanTransport`), has no mathematical consumer anywhere in the
development: it is only re-exported and audited.

## What this file supplies

The lemmas that make the printed conclusion and the Appendix-B lemma the *same
statement*, so that the route can be exchanged without touching any endpoint.

* `hsDistSq_conj_eq_hsNormSq_commutator` -- the printed "by unitary invariance
  of the normalized Hilbert--Schmidt norm": the displacement `V A V* − A` and
  the commutator `AV − VA` have the same normalized Hilbert--Schmidt norm.  This
  is the exact identity that turns the transport conclusion, which is stated as
  a commutator, into the displacement the corner chain consumes.
* `centralRoot_commutator_opNormVanishing` and
  `centralRoot_commutator_hsNormSq_vanishing` -- the transport's *hypothesis* at
  the root element: because `c` centralizes `ι(Γ)`, the microstate `V_c`
  asymptotically commutes with `V_{ι γ}`, in operator norm and hence in
  normalized Hilbert--Schmidt norm.  This is the printed "Since `c` centralizes
  `ι(Γ)`, the sequence `(W_{c,n})` centralizes `(W_{ι(γ),n})` asymptotically in
  operator norm, hence in normalized Hilbert--Schmidt norm" of
  `\label{thm:sign-criterion}`.
* `transportedRoot_displacement_of_hsCommutator` -- the drop-in: from the
  printed transport conclusion at `x_n = V_c` and `s = t`, the statement of
  `transportedRoot_displacement_hsDistSq_vanishing` follows.  The lamp
  microstate `lampMatrix B C n` is `V_t V_c V_t*`, which is exactly the
  transported vector `Ad U_n(t) x_n` of the printed conclusion, so no object is
  substituted.

## What is not here

The data-packaging step: `manuscriptKazhdanTransport` is stated over
`naturalFiniteModel (d n)`, while an `OpAlmostRepresentation` carries an
arbitrary `FiniteModel` at each stage, so feeding
`centralRoot_commutator_hsNormSq_vanishing` into it needs the reindexing
`Analysis/NaturalMatrixCoordinateEquiv.lean` provides
(`matrixReindexStarAlgEquiv`, `unitaryReindexEquiv`,
`norm_matrixReindexStarAlgEquiv`) together with the one lemma that file lacks,
invariance of `hsNormSq` under reindexing.  That is bureaucracy, not
mathematics, and it is the whole of what still separates these two routes.
-/

namespace GroupApproximation
namespace UltraproductRigidityRoute

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open scoped Matrix.Norms.L2Operator commutatorElement

noncomputable section

universe u

/-! ## Two scalar helpers -/

/-- Square roots reflect order on nonnegatives.  Used to move between the
printed `‖·‖ → 0` and the squared quantities the corner chain carries. -/
theorem le_of_sqrt_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : Real.sqrt a ≤ Real.sqrt b) : a ≤ b := by
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-! ## The printed unitary-invariance bridge -/

/-- **Unitary invariance of the normalized Hilbert--Schmidt norm, in the form
the two routes need to be compared.**

The displacement of the adjoint action and the commutator have the same
normalized Hilbert--Schmidt norm:

`‖V A V* − A‖₂ = ‖A V − V A‖₂`,

because `A V − V A = (A − V A V*) V` and right multiplication by a unitary is a
`‖·‖₂`-isometry.  The printed proof of `\label{thm:kazhdan-transport}` states its
conclusion as a commutator; the corner chain of `\label{app:finite-stage}`
states its as a displacement; this is the identity that makes them one
statement. -/
theorem hsDistSq_conj_eq_hsNormSq_commutator (Y : FiniteModel)
    {V : Matrix Y Y ℂ} (hV : V ∈ Matrix.unitaryGroup Y ℂ) (A : Matrix Y Y ℂ) :
    hsDistSq Y (V * A * Vᴴ) A = hsNormSq Y (A * V - V * A) := by
  have hVstarV : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hfactor : A * V - V * A = (A - V * A * Vᴴ) * V := by
    noncomm_ring [hVstarV]
  rw [hfactor, hsNormSq_mul_right Y hV]
  have hneg : hsNormSq Y (-(A - V * A * Vᴴ)) = hsNormSq Y (A - V * A * Vᴴ) :=
    hsNormSq_neg Y _
  show hsNormSq Y (V * A * Vᴴ - A) = hsNormSq Y (A - V * A * Vᴴ)
  rw [← hneg]
  congr 1
  abel

/-! ## The transport hypothesis at the root element -/

section Core

variable {Γ : Type} [Group Γ] {E : Type u} [Group E]

/-- **The root microstate asymptotically commutes with the Kazhdan image, in
operator norm.**  This is the printed sentence "Since `c` centralizes `ι(Γ)`,
the sequence `(W_{c,n})` centralizes `(W_{ι(γ),n})` asymptotically in operator
norm", and it is the hypothesis `thm:kazhdan-transport` is applied with.

Only `comm_c` and asymptotic multiplicativity are used: the commutator of the
two microstates is the difference of the two multiplicative defects at
`(c, ι γ)` and `(ι γ, c)`, whose group products agree because `c` and `ι γ`
commute. -/
theorem centralRoot_commutator_opNormVanishing
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    OpNormVanishing B (fun n ↦
      (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
        - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
          * B.map n C.c) := by
  have h1 := (multiplicativeDefect_vanishing B C.c (C.iota γ)).neg
  have h2 := multiplicativeDefect_vanishing B (C.iota γ) C.c
  have hcomm : C.c * C.iota γ = C.iota γ * C.c := C.comm_c γ
  refine (h1.add h2).congr fun n ↦ ?_
  show -((B.map n (C.c * C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
        - (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ))
      + ((B.map n (C.iota γ * C.c) : Matrix (B.model n) (B.model n) ℂ)
        - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * B.map n C.c)
      = _
  rw [hcomm]
  abel

/-- **The same, in normalized Hilbert--Schmidt norm.**  The printed step "hence
in normalized Hilbert--Schmidt norm" is the inequality `‖·‖₂ ≤ ‖·‖`, which needs
only that the coordinate models are nonempty.

This is exactly the hypothesis `_hx` of
`KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`, at the root element
`x_n = V_c`. -/
theorem centralRoot_commutator_hsNormSq_vanishing
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (B.model n)
        ((B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
          - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
            * B.map n C.c)) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := centralRoot_commutator_opNormVanishing B C γ ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  set M : Matrix (B.model n) (B.model n) ℂ :=
    (B.map n C.c : Matrix (B.model n) (B.model n) ℂ) * B.map n (C.iota γ)
      - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * B.map n C.c
  have hop : ‖M‖ ≤ ε := hN n hn
  have hle : hsNormSq (B.model n) M ≤ ‖M‖ * ‖M‖ :=
    hsNormSq_le_mul_self_l2_opNorm (B.model n) (B.modelNonempty n) M
  have hsq : Real.sqrt (hsNormSq (B.model n) M) ≤ Real.sqrt (‖M‖ * ‖M‖) :=
    Real.sqrt_le_sqrt hle
  rw [Real.sqrt_mul_self (norm_nonneg M)] at hsq
  exact hsq.trans hop

/-! ## The drop-in for the Appendix-B displacement lemma -/

/-- **The printed transport conclusion is the Appendix-B displacement
statement.**

The lamp microstate is `lampMatrix B C n = V_t V_c V_t*`, which is the
transported vector `Ad U_n(t) x_n` of the printed conclusion at `x_n = V_c` and
`s = t`.  Given that conclusion -- the commutator of the transported vector with
`V_{ι γ}` vanishing in normalized Hilbert--Schmidt norm -- the displacement
statement of `KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`
follows, by unitary invariance and nothing else.

So substituting this for the Appendix-B lemma inside
`compressionDefect_hsDistSq_vanishing` exchanges the route without changing any
statement in the chain, which is what rows `INT.03` and `INT.04` ask for. -/
theorem transportedRoot_displacement_of_hsCommutator
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E) (γ : Γ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      Real.sqrt (hsNormSq (B.model n)
        (lampMatrix B C n
            * (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
          - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
            * lampMatrix B C n)) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      hsDistSq (B.model n)
        ((B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          lampMatrix B C n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        (lampMatrix B C n) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [hsDistSq_conj_eq_hsNormSq_commutator (B.model n)
    (B.map n (C.iota γ)).2 (lampMatrix B C n)]
  exact le_of_sqrt_le_sqrt (hsNormSq_nonneg _ _) hε.le (hN n hn)

end Core

end

end UltraproductRigidityRoute
end GroupApproximation
