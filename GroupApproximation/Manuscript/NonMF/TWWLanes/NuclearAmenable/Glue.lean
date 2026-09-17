import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.LocalAmenable
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-13, part 2: glue for `NuclearAmenableTraceInput`, separable form

## Truth check: the unrestricted structure is FALSE, so the separable restriction is necessary

`QuasidiagonalMF.NuclearAmenableTraceInput` (Analysis/TikuisisWhiteWinterCore.lean:192)
quantifies over **all** nuclear `A : Type u`.  In the sequence form of
`Quasidiagonal.IsAmenableTrace` that is false.  A model `(φₙ)` induces a ⋆-homomorphism
from `A` into `ℓ^∞(M_{kₙ}) / {2-norm null}`.  This homomorphism is injective when `τ`
is faithful: if `‖φₙ a‖₂ → 0`, then `τ(a⋆a) = lim tr(φₙ a⋆ φₙ a) = 0`.  The target
has cardinality at most `𝔠`.  Now take `A = C({0,1}^κ)` with `κ > 𝔠`, which is
commutative and hence nuclear, and let `τ` be integration against the product measure,
which has full support and so is faithful.  Then `|A| > 𝔠`, and no model exists.
The field is used only for separable `A` (`isQuasidiagonalTrace_of_core`), so the
endpoint here is the separable-restricted `NuclearAmenableTraceSeparableStatement`.
The last theorem in this file shows that it suffices for that consumer.

## Pitfall in the lanes-file sketch of nm-tww-11

The sketch has the hypothesis use `π : A →⋆ₐ B(H)` with `H` finite-dimensional.  Read
literally, nm-tww-12 is then false.  UHF algebras such as `M_{2^∞}` are separable,
nuclear, have a faithful trace, and have no finite-dimensional representation.  The
interface below therefore uses a **ucp** map into matrices.  It adds a `2`-norm
multiplicativity clause weighted by the density, and replaces the ‖·‖₁ commutator of `d`
by the ‖·‖₂ commutator of `T = d^{1/2}`.

## The gap: two literature Statements, stated as interfaces for nm-tww-11 and nm-tww-12

* `ConnesTrickStatement` (nm-tww-11) is **true**.  Let `d = T²` have spectral layers
  `e_t = χ_{(t,∞)}(d)`.  Take the direct sum over `t` of the compressions
  `e_t φ(·) e_t`, with (rationally approximated) multiplicities `dt`.  The normalized
  trace is `tr(T φ(·) T)` because `∫ e_t dt = d`.  The squared defect is at most
  `2‖DT‖₂² + 2‖a‖²∫‖[e_t, φ b]‖₂² dt`.  The layer-cake identity gives
  `∫‖[e_t, x]‖₂² dt = Σ|μᵢ² − μⱼ²| |xᵢⱼ|² ≤ 2‖x‖ ‖[T, x]‖₂`.
* `NuclearTraceApproxDensityStatement` (nm-tww-12) is **true**.  By Brown–Ozawa,
  Thm 6.2.7, every trace on a nuclear algebra is amenable, which gives local ucp models.
  Then take `T = k^{-1/2}·1`: it commutes with everything, `tr(TφT) = normTrace φ`, and
  `‖DT‖₂² = hsNormSq D`.

Both are strictly smaller in proof content than the target.  The passage from local to
sequence form (a diagonal argument over a dense sequence, the Lipschitz bound on `τ` out
of ucp contractivity, and the dense-generator upgrade) is **proved** in `LocalAmenable`.
The composition is proved here.  These Statements are interfaces, not results.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearAmenable

open Matrix Quasidiagonal

noncomputable section

universe u

/-- **Approximately invariant densities for `τ`.**  For every finite `F` and `ε > 0` there
is a ucp map `φ` into a matrix algebra and a Hermitian `T` with `tr(T²) = 1`
(unnormalized trace).  The following all hold on `F` up to `ε`:
* the vector-state trace: `‖τ x − tr(T φ(x) T)‖ ≤ ε`;
* the commutator: `‖φ(x) T − T φ(x)‖₂² ≤ ε`;
* weighted multiplicativity: `‖(φ(xy) − φ(x)φ(y)) T‖₂² ≤ ε`.

Here `‖M‖₂² = re tr(Mᴴ M)` is unnormalized. -/
def HasApproxInvariantDensities {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ) (T : Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧ T.IsHermitian ∧
      Matrix.trace (T * T) = 1 ∧
      (∀ x ∈ F, ‖τ x - Matrix.trace (T * φ x * T)‖ ≤ ε) ∧
      (∀ x ∈ F, (Matrix.trace ((φ x * T - T * φ x)ᴴ * (φ x * T - T * φ x))).re ≤ ε) ∧
      (∀ x ∈ F, ∀ y ∈ F,
        (Matrix.trace (((φ (x * y) - φ x * φ y) * T)ᴴ *
          ((φ (x * y) - φ x * φ y) * T))).re ≤ ε)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.HasApproxInvariantDensities

/-- **Interface for lane nm-tww-11 (Connes' trick).**  Approximately invariant densities
give a locally amenable trace.  This is an assumed Statement, not a result.  The module
docstring sketches why it is true. -/
def ConnesTrickStatement : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A) (τ : A → ℂ),
    HasApproxInvariantDensities τ → IsLocallyAmenableTrace τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.ConnesTrickStatement

/-- **Interface for lane nm-tww-12.**  On a separable nuclear C⋆-algebra, every faithful
tracial state has approximately invariant densities.  This is an assumed Statement, not a
result.  It is true by Brown–Ozawa Thm 6.2.7, with `T = k^{-1/2}·1`. -/
def NuclearTraceApproxDensityStatement : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A →
    CStarExactness.IsNuclearCStarAlgebra A →
      ∀ τ : FaithfulTracialState A, HasApproxInvariantDensities (fun a : A ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.NuclearTraceApproxDensityStatement

/-- **The single remaining gap, in local form.**  Every faithful tracial state on a
separable nuclear C⋆-algebra is locally amenable.  It is strictly smaller in proof
content than `NuclearAmenableTraceSeparableStatement`, since the diagonal argument
`isAmenableTrace_of_isLocallyAmenableTrace` is proved.  It is true by Brown–Ozawa
Thm 6.2.7. -/
def NuclearLocallyAmenableTraceStatement : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A →
    CStarExactness.IsNuclearCStarAlgebra A →
      ∀ τ : FaithfulTracialState A, IsLocallyAmenableTrace (fun a : A ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.NuclearLocallyAmenableTraceStatement

/-- **The field of `NuclearAmenableTraceInput`, restricted to separable algebras.**  The
module docstring explains why the unrestricted field is false. -/
def NuclearAmenableTraceSeparableStatement : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A), TopologicalSpace.SeparableSpace A →
    CStarExactness.IsNuclearCStarAlgebra A →
      ∀ τ : FaithfulTracialState A, IsAmenableTrace (fun a : A ↦ τ a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.NuclearAmenableTraceSeparableStatement

/-- nm-tww-12 composed with nm-tww-11 gives the local gap. -/
theorem nuclearLocallyAmenableTrace_of_connesTrick_of_nuclearDensity
    (h11 : ConnesTrickStatement.{u}) (h12 : NuclearTraceApproxDensityStatement.{u}) :
    NuclearLocallyAmenableTraceStatement.{u} :=
  fun A inst hsep hnuc τ ↦ h11 A inst (fun a : A ↦ τ a) (h12 A inst hsep hnuc τ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.nuclearLocallyAmenableTrace_of_connesTrick_of_nuclearDensity

/-- **Local ⟹ sequence form, for all separable nuclear algebras.**  This is proved by
the diagonal argument `isAmenableTrace_of_isLocallyAmenableTrace`. -/
theorem nuclearAmenableTraceSeparable_of_nuclearLocallyAmenableTrace
    (h : NuclearLocallyAmenableTraceStatement.{u}) :
    NuclearAmenableTraceSeparableStatement.{u} :=
  fun A inst hsep hnuc τ ↦
    isAmenableTrace_of_isLocallyAmenableTrace hsep τ.toLinearMap τ.map_one
      (h A inst hsep hnuc τ)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.nuclearAmenableTraceSeparable_of_nuclearLocallyAmenableTrace

/-- **The lane endpoint.**  nm-tww-11 and nm-tww-12 give the separable-restricted field
of `NuclearAmenableTraceInput`. -/
theorem nuclearAmenableTraceSeparable_of_connesTrick_of_nuclearDensity
    (h11 : ConnesTrickStatement.{u}) (h12 : NuclearTraceApproxDensityStatement.{u}) :
    NuclearAmenableTraceSeparableStatement.{u} :=
  nuclearAmenableTraceSeparable_of_nuclearLocallyAmenableTrace
    (nuclearLocallyAmenableTrace_of_connesTrick_of_nuclearDensity h11 h12)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.nuclearAmenableTraceSeparable_of_connesTrick_of_nuclearDensity

/-- The structure implies the separable Statement.  So the restriction only weakens
what is assumed. -/
theorem nuclearAmenableTraceSeparable_of_nuclearAmenableTraceInput
    (h : QuasidiagonalMF.NuclearAmenableTraceInput.{u}) :
    NuclearAmenableTraceSeparableStatement.{u} :=
  fun A inst _ hnuc τ ↦ h.amenableTrace A inst hnuc τ

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.nuclearAmenableTraceSeparable_of_nuclearAmenableTraceInput

/-- **The separable Statement is enough for its only consumer.**  This is
`QuasidiagonalMF.isQuasidiagonalTrace_of_core`, with the unrestricted structure replaced
by `NuclearAmenableTraceSeparableStatement`. -/
theorem isQuasidiagonalTrace_of_separableConnes_of_core {UCT : Type u → Prop}
    (connes : NuclearAmenableTraceSeparableStatement.{u})
    (core : QuasidiagonalMF.TikuisisWhiteWinterCoreInput.{u} UCT)
    (A : Type u) [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A)
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A)
    (huct : UCT A) (τ : FaithfulTracialState A) :
    IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep
    (core.locallyQuasidiagonal A inferInstance hsep hnuc huct τ
      (connes A inferInstance hsep hnuc τ))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearAmenable.isQuasidiagonalTrace_of_separableConnes_of_core

end

end Manuscript.NonMF.TWWLanes.NuclearAmenable
end GroupApproximation
