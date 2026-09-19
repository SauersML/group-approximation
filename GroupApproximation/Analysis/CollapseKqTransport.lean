import GroupApproximation.Analysis.CollapseInvariantSubspace

/-!
# The fixed-space transport, read inside `K_q`

Proof-ledger row `CO.21b`.  The printed last paragraph of
`thm:projection-collapse` runs Delorme–Guichardet on `π` restricted to the
closed invariant subspace `K_q`, and
`Analysis/CollapseInvariantSubspace.collapse_contradiction_Kq` runs it there.
Three of its four printed clauses are proved at that generality.  The fourth,
the transport — *"the transport chain identifies that fixed space with
`Fix π(L)` at the weight `k_n`"* — is a binder there, and the row records
exactly why:

> The derivation is `CollapseTransportEndpoint.transport_corona`, which needs a
> `KazhdanCompressionRep` bundle, and
> `CollapseDelormeCorona.collapse_contradiction_corona_delorme` already
> discharges it for that bundle — on `K_ω`.  What is not built is the `K_q`
> counterpart of that discharge, which wants the fixed-space comparison read
> inside the subspace rather than in the ambient, and it is the only clause of
> the printed paragraph that `K_q` does not yet carry.

This file builds it, and the answer is that the comparison does not have to be
redone inside the subspace at all: it is inherited.

## Why the transport restricts, and why that is not a weakening

A transport statement says that a vector fixed by the compressed elements
`π(c a)` is fixed by all of `π`.  Both the hypothesis and the conclusion are
equations between vectors, and the inclusion `K_q → K_ω` is injective and
intertwines the two representations on the nose — that is exactly what
`restrictUnitary` is, and `coe_restrictUnitary` is the intertwining, by
`rfl`.  So a vector of `K_q` fixed by the compressed elements *inside* `K_q` is
fixed by them *in* `K_ω`, the ambient statement applies to it, and the
resulting ambient equations descend because the inclusion is injective.

Nothing is lost in either direction and no estimate enters.  The point is not
that the subspace statement is weaker — it is that the ambient chain already
proves the subspace statement, so the printed paragraph on `K_q` needs no
hypothesis the printed paragraph on `K_ω` did not already have.

`collapse_contradiction_Kq_of_ambient` is `collapse_contradiction_Kq` with its
transport binder moved to ambient strength, which is the strength
`Analysis/CollapseTransportEndpoint.transport_corona` supplies, and
`printed_collapse_contradiction_Kq_of_ambient` is the same for the printed
displacement family of `CO.21`.
-/

namespace GroupApproximation
namespace CollapseKqTransport

open Filter Matrix Topology
open UltraproductModelConstruction RankNormalizedHilbertization
open KOmegaHilbert CollapseCocycleAnalytic CollapseUltraproductRepresentation
open RankNormalizedLambda CollapseLambdaCocycle CollapseInvariantSubspace
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

/-! ## The general restriction -/

section Restrict

variable {G : Type u} [Group G] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **A fixed-vector transport restricts to any invariant subspace.**

If every vector of the ambient space fixed by `π ∘ c` is fixed by all of `π`,
the same holds inside an invariant subspace `U`, for the restricted
representation.  The proof is the injectivity of `U → E` in both directions:
`coe_restrictUnitary` turns each equation in `U` into the corresponding
equation in `E` and `Subtype.ext` turns it back. -/
theorem restrictUnitary_transport (π : G →* (E ≃ₗᵢ[ℂ] E)) (U : Submodule ℂ E)
    (hU : ∀ g : G, ∀ x ∈ U, π g x ∈ U) (c : G → G)
    (hambient : ∀ x : E, (∀ a : G, π (c a) x = x) → ∀ g : G, π g x = x) :
    ∀ y : U, (∀ a : G, restrictUnitary π U hU (c a) y = y) →
      ∀ g : G, restrictUnitary π U hU g y = y := by
  intro y hy g
  refine Subtype.ext ?_
  rw [coe_restrictUnitary]
  refine hambient (y : E) (fun a ↦ ?_) g
  have h := congrArg (fun z : U ↦ (z : E)) (hy a)
  rwa [coe_restrictUnitary] at h

end Restrict

/-! ## The collapse endpoint at ambient transport strength -/

section Endpoint

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
variable {H : Type u} [Group H]

/-- **The transport hypothesis of `collapse_contradiction_Kq`, from the
ambient one.**  Stated separately because it is the whole content of the
clause `CO.21b` records as missing: the fixed-space comparison inside `K_q` is
the ambient comparison, restricted. -/
theorem transport_Kq_of_ambient (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (c : H → H)
    (hambient : ∀ x : KRank Y P ω,
      (∀ a : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ (c a) x
        = x) →
      ∀ g : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g x = x) :
    ∀ y : Kq Y P ω hω,
      (∀ a : H, conjRepKq Y P ω hω Θ (c a) y = y) →
        ∀ g : H, conjRepKq Y P ω hω Θ g y = y :=
  restrictUnitary_transport
    (conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ) (Kq Y P ω hω)
    (fun g x hx ↦ conjRep_mem_Kq Y P ω hω Θ g x hx) c hambient

/-- **`CO.21b`'s printed paragraph on `K_q`, with no transport binder beyond
the ambient one.**

`collapse_contradiction_Kq` asks for the transport inside `K_q`; this asks for
it in `K_ω`, which is the form
`Analysis/CollapseTransportEndpoint.transport_corona` proves and
`CollapseDelormeCorona.collapse_contradiction_corona_delorme` already consumes.
So the printed paragraph read inside the printed space costs no hypothesis
that the same paragraph read in the ambient did not already cost. -/
theorem collapse_contradiction_Kq_of_ambient (P : MatFam Y)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{u, u} H)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (d : H → rankIdeal Y P) (c : H → H)
    (hd : ∀ g h : H, (d (g * h) : NormMatrixCStarCorona (fun n ↦ Y n))
      = (d g : NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g))))
    (hcompressed : ∀ a : H, lambda Y P ω hω (d (c a)) = 0)
    (hambient : ∀ x : KRank Y P ω,
      (∀ a : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ (c a) x
        = x) →
      ∀ g : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g x = x)
    (hne : ∃ g : H, lambda Y P ω hω (d g) ≠ 0) : False :=
  collapse_contradiction_Kq Y P ω hω hT Θ d c hd hcompressed
    (transport_Kq_of_ambient Y P ω hω Θ c hambient) hne

/-- **`CO.21` and `CO.21b` joined at the printed objects, with the transport at
ambient strength.**  The printed displacement family, the printed space, the
printed representation, and no clause of the printed paragraph left as a
binder that the ambient route does not also carry. -/
theorem printed_collapse_contradiction_Kq_of_ambient (P : MatFam Y)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (hT : HasKazhdanPropertyT.{u, u} H)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n)) (c : H → H)
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P)
    (hcompressed : ∀ a : H,
      lambda Y P ω hω (printedDisplacement Y P Θ p hmem (c a)) = 0)
    (hambient : ∀ x : KRank Y P ω,
      (∀ a : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ (c a) x
        = x) →
      ∀ g : H, conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g x = x)
    (hne : ∃ g : H,
      lambda Y P ω hω (printedDisplacement Y P Θ p hmem g) ≠ 0) : False :=
  printed_collapse_contradiction_Kq Y P ω hω hT Θ p c hmem hcompressed
    (transport_Kq_of_ambient Y P ω hω Θ c hambient) hne

end Endpoint

end

end CollapseKqTransport
end GroupApproximation
