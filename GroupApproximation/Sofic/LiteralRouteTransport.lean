import GroupApproximation.Sofic.GeneralModelKazhdanTransport
import GroupApproximation.Sofic.TransportShapeBridges

/-!
# Forward transport by the printed route, at the consumers' own signature

Proof-ledger rows `FN.03` and `ID.05` ask the consumers of Kazhdan transport to
invoke the literal Section-3 theorem rather than the Appendix-B surrogate.
`transport_literal` below is that: the statement of
`KazhdanAsymptoticCommutant.transport`, character for character, proved from
`GeneralModelTransport.generalModelKazhdanTransport` — hence from
`manuscriptKazhdanTransport`, hence from the printed norm-ultraproduct
argument.

## Why this is a new declaration and not an edit to `transport`

`KazhdanAsymptoticCommutant.transport` cannot simply be repointed, because it
is not only a consumer of the route — it is the *engine of the second printed
proof*.  `ManuscriptKazhdanTransport.finiteStageKazhdanTransport`, which the
manuscript announces at `\label{rem:finite-stage}` and proves at
`\label{app:finite-stage}`, is built on `transport` (its line 208,
`have hy_sq := transport B C x hx_sq hbound'`).  Rewiring `transport` onto the
ultraproduct route would therefore leave the manuscript claiming two
independent proofs of `thm:kazhdan-transport` while the corpus contained one,
wearing two names.  That is the exact defect class this audit exists to catch,
so the finite-stage engine is left alone and the literal route is added beside
it.

The two are deliberately interchangeable: identical statement, identical
hypotheses, different proof.  A consumer picks its route by picking its name.

## The two shape changes, and why neither costs anything

The consumers state the asymptotic-commutant condition as the *conjugation
defect* `x − u x u*` in squared form; the manuscript's theorem states it as the
*commutator* `x u − u x` in unsquared form.  Both gaps are closed exactly, by
`TransportShapeBridges`: `hsNormSq_conjugation_defect` because
`x − u x u* = (x u − u x) u*` and right multiplication by a unitary is an
isometry for the normalized Hilbert--Schmidt norm, and the `ε` versus `ε²`
pairing because the two quantifications are the same convergence.  No estimate
is introduced and no constant is lost.  `finiteStageKazhdanTransport` performs
these same two conversions inline, in the opposite direction, which is the
in-repo precedent for both.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

-- Mirrors the `open` block of `Sofic/KazhdanAsymptoticCommutant.lean`, whose
-- namespace this file re-enters: the adjoint postfix and the matrix operator
-- norm are both scoped notation.
open Matrix
open scoped Matrix.Norms.L2Operator
open GroupApproximation.GeneralModelTransport

universe u w

/-- **Forward Kazhdan transport, by the printed route.**  Statement-identical
to `KazhdanAsymptoticCommutant.transport`, proved from the literal Section-3
theorem instead of the finite-stage machinery. -/
theorem transport_literal
    {Γ : Type} [Group Γ] {E : Type u} [Group E]
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsUniformlyBounded B x) :
    IsAsymptoticCommutant B C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  have hT : HasKazhdanPropertyTComplex.{0, w} Γ :=
    hasKazhdanPropertyT_iff_textbook.mp C.kazhdan
  have hY : ∀ n, 0 < Fintype.card (B.model n) := fun n ↦
    Fintype.card_pos_iff.mpr (B.modelNonempty n)
  -- The hypothesis, moved from the conjugation defect onto the commutator.
  have hxgen : ∀ γ : Γ,
      GeneralHSCommutatorVanishing B.model B.map x (C.iota γ) := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
        ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
    -- Ascribing the type here beta-reduces `(fun n ↦ …) n` by `exact`.
    have hdef : hsNormSq (B.model n)
        (x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)
        ≤ ε ^ 2 := hN n hn
    rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu (x n)]
      at hdef
    exact TransportShapeBridges.sqrt_hsNormSq_le_of_le_sq (B.model n) _
      hε.le hdef
  -- The printed theorem, over the consumer's own model family.
  have hmain := generalModelKazhdanTransport hT C.iota C.t C.compresses
    B.model hY B.map B.asymptoticallyMultiplicative x hbound hxgen
  -- The conclusion, moved back onto the conjugation defect.
  intro γ ε hε
  obtain ⟨N, hN⟩ := hmain γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hu : (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)
      ∈ Matrix.unitaryGroup (B.model n) ℂ := (B.map n (C.iota γ)).2
  have hcomm : Real.sqrt (hsNormSq (B.model n)
      (((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ)))
      ≤ Real.sqrt ε := hN n hn
  have hsq := TransportShapeBridges.hsNormSq_le_sq_of_sqrt_le (B.model n) _
    (Real.sqrt_nonneg ε) hcomm
  rw [Real.sq_sqrt hε.le] at hsq
  show hsNormSq (B.model n)
      (((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) -
        (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ) *
          ((B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) *
          (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ) ≤ ε
  rw [TransportShapeBridges.hsNormSq_conjugation_defect (B.model n) hu _]
  exact hsq

end KazhdanAsymptoticCommutant
end GroupApproximation
