import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Analysis.KKTheoryKasparov
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.FaithfulTracialState
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-14, part 1: the trace-kernel extension lifting interface

Schafhauser's route to Tikuisis--White--Winter passes through two ultraproducts of
matrix algebras over the same finite models `X n`:

* the **tracial** matrix ultraproduct `∏_ω (M_{X n}, tr)`, which is
  `TracialUltraproduct.TracialMatrixQuotient X ω`. Amenable traces give trace-preserving
  `⋆`-homomorphisms into it (lane `nm-tww-06`);
* the **norm** matrix corona `ℓ∞(M_{X n}) / c₀(M_{X n})`, which is `NormMatrixCStarCorona`.
  It maps onto the tracial ultraproduct by the trace-kernel quotient
  `TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω`.

The lifting theorem is the step from the first kind of homomorphism to the second. The
kernel of the quotient is the trace-kernel ideal, and the `KK`/UCT input is used exactly
here.

## Shape (cartographer pitfall)

The interface lives at the matrix-sequence ultraproduct and not at `Q_ω`. The conclusion
is **existential** in the new models `X'` and the new ultrafilter `ω'`: we do not require
the same `X`. With this shape the Tikuisis--White--Winter theorem implies the interface,
so it is not false. See `TraceKernelLiftStatement` below.

The lane prints the statement as `∀ X ω θ, (trace-compatible θ) → ∃ X' ω' Φ, …`. This
file writes it in curried form as `HasTraceCompatibleUltraHom τ → HasTraceCompatibleCoronaHom
τ`. The two forms are logically the same. `TracialUltraproduct.ultratrace` is the additive
map underlying `ultratraceCLM`, and `ultratraceCLM_apply` is `rfl`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace TraceKernelInterface

noncomputable section

universe u

/-- **A trace-compatible homomorphism into a tracial matrix ultraproduct.** There are
nonempty finite models `X n`, an ultrafilter `ω` on `ℕ`, and a unital `⋆`-homomorphism
`θ : A → ∏_ω (M_{X n}, tr)` whose ultratrace recovers `τ`.

The ultrafilter is arbitrary, exactly as in the lane statement (`∀ X ω θ`). -/
def HasTraceCompatibleUltraHom {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∃ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) (ω : Ultrafilter ℕ),
    letI : ∀ n, Nonempty (X n) := hne
    ∃ θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ),
      ∀ a : A, TracialUltraproduct.ultratrace X ω (θ a) = τ a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.HasTraceCompatibleUltraHom

/-- **A trace-compatible homomorphism into a norm matrix corona.** There are nonempty
finite models `X n`, a nonprincipal ultrafilter `ω` (`ω ≤ cofinite`), and a unital
`⋆`-homomorphism `Φ : A → ℓ∞(M_{X n}) / c₀(M_{X n})`. Pushing `Φ` through the trace-kernel
quotient into `∏_ω (M_{X n}, tr)` and then taking the ultratrace recovers `τ`.

This is the hypothesis of the lane `nm-tww-09` criterion
`LiftCriterion.isQuasidiagonalTrace_of_traceKernelLift_ucpCoordinates`. -/
def HasTraceCompatibleCoronaHom {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∃ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ Filter.cofinite),
    letI : ∀ n, Nonempty (X n) := hne
    ∃ Φ : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n),
      ∀ a : A, TracialUltraproduct.ultratrace X ω
        (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient X ω hω (Φ a)) = τ a

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.HasTraceCompatibleCoronaHom

/-- **The trace-kernel extension lifting theorem, as an interface (lane nm-tww-14).**

Let `UCT` be a predicate on separable C⋆-algebras, for example `T.SatisfiesUCT` for a
Kasparov theory `T`. Let `S` be separable, nuclear and `UCT`, and let `τ` be a faithful
tracial state on `S`. Suppose some unital `⋆`-homomorphism `θ : S → ∏_ω (M_{X n}, tr)` has
ultratrace `τ`. Then **some** unital `⋆`-homomorphism `Φ : S → ℓ∞(M_{X' n}) / c₀(M_{X' n})`,
for some possibly different models `X'` and nonprincipal ultrafilter `ω'`, is
trace-compatible with `τ` after the trace-kernel quotient.

**Truth.** At Kasparov's genuine `KK`, Tikuisis--White--Winter (Annals 2017) makes `τ` a
quasidiagonal trace. Choose ucp models `ψₙ : S → M_{kₙ}` that are asymptotically
multiplicative in operator norm and whose traces tend to `τ`, with `kₙ ≥ 1`. The sequence
`(ψₙ(a))ₙ` is bounded, and it defines a unital `⋆`-homomorphism into the norm corona.
Its ultratrace along any nonprincipal `ω'` is `τ`. So the conclusion holds even without
the hypothesis `θ`. This is why the conclusion must be existential in `X'` and `ω'`.

**Degenerate model.** At `RelatedTWW.trivialKasparovTheory`, every separable algebra
satisfies the UCT. There the interface is the UCT-free lifting statement, and together
with the upstream lanes it would give quasidiagonality of every faithful trace on every
separable nuclear C⋆-algebra. That is an **open problem**, the UCT-free
Tikuisis--White--Winter question. So the interface can only be discharged at a real `KK`.
See `Reduction.lean`. -/
def TraceKernelLiftStatement (UCT : KK.SepCStarAlgebra.{u} → Prop) : Prop :=
  ∀ S : KK.SepCStarAlgebra.{u}, CStarExactness.IsNuclearCStarAlgebra S → UCT S →
    ∀ τ : FaithfulTracialState S,
      HasTraceCompatibleUltraHom (fun a : S ↦ τ a) →
        HasTraceCompatibleCoronaHom (fun a : S ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.TraceKernelInterface.TraceKernelLiftStatement

end

end TraceKernelInterface
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
