import GroupApproximation.Sofic.TensorPowerTransport
import GroupApproximation.Sofic.TransportVariantsAnyUniverse

/-!
# The fixed-tensor sentence with the Kazhdan source in any universe

**The fixed-tensor paragraph was cut from the manuscript on 2026-08-18**,
with the intertwiner clause of `thm:transport-variants` (see the change-history
table of `notes/NON_MF_PROOF_LEDGER.md`); no badge is owed for this module.  The
quotation below is kept as a record.  The paragraph read

> Invariant tensors of type `(p,q)` may be identified with Hilbert--Schmidt
> intertwiners from the `q`th to the `p`th tensor power. … tensor powers of an
> operator-norm asymptotic representation are again operator-norm asymptotic
> representations, and Theorem~\ref{thm:transport-variants}(2) applies to every
> pair of them: at each fixed tensor type and each weight, a sequence
> asymptotically invariant for the conjugate copy of the Kazhdan image is
> already asymptotically invariant for the whole of it.

and `thm:transport-variants` inherits its groups from `thm:kazhdan-transport`,
which says only "let `Γ` and `H` be groups" — no countability, no universe.
`TensorPowerTransport.manuscriptFixedTensorTransport` fixed the source at
`Type 0`; that was ledger row `TV.12`, retired with the paragraph.

The row closes with no new mathematics, because the paragraph is explicit that
it *is* `thm:transport-variants`(2) instantiated at `B₁ = U^{⊗p}`,
`B₂ = U^{⊗q}`, and that variant is already available at every source universe as
`TransportVariantsAnyUniverse.scaled_intertwiner_transport_anyUniverse` (the retired ledger
rows `TV.02`/`TV.03`).  The tensor-power construction
`OpAlmostRepresentation.tensorPow` never mentions the source group, so the
instantiation is the same one line it was at `Type 0`.
-/

namespace GroupApproximation
namespace TensorPowerTransport

open Matrix IntertwinerKazhdanTransport
open scoped Matrix.Norms.L2Operator

universe u v

/-- **The fixed-tensor transport statement with the Kazhdan source at an
arbitrary universe** (ledger row `TV.12`).

Closed form: nothing to the left of the colon, every hypothesis a quantified
antecedent of the printed sentence.  A fixed tensor of type `(p, q)` is a
Hilbert--Schmidt intertwiner from the `q`-th to the `p`-th tensor power, both of
which are operator-norm almost representations of the ambient group; the
one-sided compressor of a Kazhdan datum carries every weighted asymptotic
intertwiner of any fixed type to another one, so compression creates no
asymptotic invariant tensors of that type, at any weight.

Neither group carries a countability or universe hypothesis, exactly as the
paragraph's source `thm:kazhdan-transport` states it: the datum's property `(T)`
supplies whatever countability the descent consumes. -/
theorem manuscriptFixedTensorTransport_anyUniverse :
    ∀ {Γ : Type v} {E : Type u} [Group Γ] [Group E]
      (A : OpAlmostRepresentation E)
      (p q : ℕ) (w : ℕ → ℝ), (∀ n, 0 ≤ w n) →
      ∀ (C : KazhdanCompressionCore Γ E)
        (x : ∀ n, Matrix ((A.tensorPow p).model n)
          ((A.tensorPow q).model n) ℂ),
        IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w
            C.iota x →
          IsScaledRectMassBounded (A.tensorPow p) (A.tensorPow q) w x →
          IsScaledAsymptoticIntertwinerOf (A.tensorPow p) (A.tensorPow q) w
            C.iota
            (fun n ↦
              ((A.tensorPow p).map n C.t :
                  Matrix ((A.tensorPow p).model n)
                    ((A.tensorPow p).model n) ℂ) *
                x n *
                ((A.tensorPow q).map n C.t :
                  Matrix ((A.tensorPow q).model n)
                    ((A.tensorPow q).model n) ℂ)ᴴ) := by
  intro Γ E _ _ A p q w hw C x hx hbound
  exact TransportVariantsAnyUniverse.scaled_intertwiner_transport_anyUniverse
    (A.tensorPow p) (A.tensorPow q) w hw C x hx hbound

end TensorPowerTransport
end GroupApproximation
