import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingAmenable
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingTraceKernel

/-!
# Trace-preserving embeddings into `Q^ω` with ucp lifts: the consumer interface

Lane TWWSchafhauser-3b (work order WO-TWWCore-3, piece 3b).  The sources are
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. 759 (2020), §2--3, and Brown--Ozawa, Ch. 6.

`TracialEmbedding τ X ω` packages what the later pieces (3c: the extension by the
trace-kernel ideal; 3d: lifting through it) consume:

* ucp maps `φ_n : A → M_{X n}`, assembled into a linear lift
  `lift : A → ℓ∞(M_{X n})` with `lift a n = φ_n a`;
* a unital ⋆-homomorphism `hom : A → Q^ω = TracialMatrixQuotient X ω` with
  `hom a = [lift a]`;
* trace preservation `tr_ω ∘ hom = τ`.

Proved here:

* `hasTracialEmbedding_of_isAmenableTrace`: every normalized amenable trace has
  one, along a free ultrafilter `ω ≤ cofinite`.
* `TracialEmbedding.hom_injective`: when `τ` is a faithful tracial state, `hom` is
  injective, so `A` embeds in `Q^ω`.
* `TracialEmbedding.norm_lift_le`: the lift is contractive.
* `TracialEmbedding.traceKernelQuotient_mk_lift`: `hom` factors through the norm
  corona `Q_ω` as `π ∘ [lift]`, where `π = traceKernelQuotient`.

For a separable nuclear `A` with a faithful tracial state, the amenability input is
the Connes--Haagerup theorem (Brown--Ozawa, Thm 6.2.7).  It is not proved in this
file.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-- **A trace-preserving ⋆-homomorphism into the tracial matrix ultraproduct,
with a ucp lift** (Schafhauser 2020, §3). -/
structure TracialEmbedding {A : Type u} [CStarAlgebra A] (τ : A → ℂ)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ) where
  /-- The coordinate maps `φ_n : A → M_{X n}`. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ
  /-- Each coordinate map is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each coordinate map is completely positive. -/
  completelyPositive : ∀ n : ℕ, Quasidiagonal.IsCompletelyPositiveOnMatrices (X n) ⇑(map n)
  /-- The assembled lift `A → ℓ∞(M_{X n})`. -/
  lift : A →ₗ[ℂ] TracialUltraproduct.ModelBoundedSequence X
  /-- The coordinates of the lift are the maps `φ_n`. -/
  lift_apply : ∀ (a : A) (n : ℕ), lift a n = map n a
  /-- The unital ⋆-homomorphism into `Q^ω`. -/
  hom : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)
  /-- `hom` is the class of the lift. -/
  hom_apply : ∀ a : A,
    hom a = TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ) (lift a)
  /-- `hom` preserves the trace. -/
  trace : ∀ a : A, TracialUltraproduct.ultratraceCLM X ω (hom a) = τ a

/-- `τ` admits a trace-preserving embedding into some `Q^ω` along a free ultrafilter,
with a ucp lift. -/
def HasTracialEmbedding {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∃ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) (ω : Ultrafilter ℕ),
    (ω : Filter ℕ) ≤ cofinite ∧ Nonempty (@TracialEmbedding A _ τ X hne ω)

/-- **An amenable trace gives a trace-preserving ⋆-homomorphism into `Q^ω` with a
ucp lift** (Schafhauser 2020, §3; Brown--Ozawa, Ch. 6).  The ultrafilter is any
free ultrafilter, and the models are shifted past the empty ones. -/
theorem hasTracialEmbedding_of_isAmenableTrace {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    (h : Quasidiagonal.IsAmenableTrace τ) (hone : τ 1 = 1) : HasTracialEmbedding τ := by
  obtain ⟨M⟩ := h
  obtain ⟨K, hK⟩ := exists_tail_card_pos M hone
  have hne : ∀ n, Nonempty (tailSpace M K n) := fun n =>
    Fintype.card_pos_iff.mp (hK (n + K) (Nat.le_add_left K n))
  have hω : ((Ultrafilter.of (atTop : Filter ℕ) : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
    Ultrafilter.of_le atTop
  refine ⟨tailSpace M K, hne, Ultrafilter.of atTop, ?_, ⟨?_⟩⟩
  · rw [Nat.cofinite_eq_atTop]
    exact hω
  · exact
      { map := fun n => M.map (n + K)
        map_one := fun n => M.map_one (n + K)
        completelyPositive := fun n => M.completelyPositive (n + K)
        lift := tailLift M K
        lift_apply := fun a n => tailLift_apply M K a n
        hom := tailHom M K ((Ultrafilter.of atTop : Ultrafilter ℕ) : Filter ℕ) hω
        hom_apply := fun a =>
          tailHom_apply M K ((Ultrafilter.of atTop : Ultrafilter ℕ) : Filter ℕ) hω a
        trace := fun a => ultratraceCLM_tailHom M K (Ultrafilter.of atTop) hω a }

/-- A faithful tracial state with an amenable underlying trace admits a tracial
embedding. -/
theorem hasTracialEmbedding_of_faithfulTracialState {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A) (h : Quasidiagonal.IsAmenableTrace (fun a : A => τ a)) :
    HasTracialEmbedding (fun a : A => τ a) :=
  hasTracialEmbedding_of_isAmenableTrace h τ.apply_one

namespace TracialEmbedding

variable {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}

/-- The lift is contractive. -/
theorem norm_lift_le (E : TracialEmbedding τ X ω) (a : A) : ‖E.lift a‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) fun n => by
    rw [E.lift_apply a n]
    exact Quasidiagonal.ucp_norm_le (E.map n) (E.map_one n) (E.completelyPositive n) a

/-- `hom` factors through the norm corona: it is the trace-kernel quotient of the
corona class of the lift. -/
theorem traceKernelQuotient_mk_lift (E : TracialEmbedding τ X ω)
    (hω : (ω : Filter ℕ) ≤ cofinite) (a : A) :
    traceKernelQuotient X ω hω (normMatrixCStarCoronaMk (fun n => X n) (E.lift a))
      = E.hom a := by
  rw [traceKernelQuotient_mk, E.hom_apply]

end TracialEmbedding

/-- **A faithful trace makes the embedding injective.**  `A` then embeds as a
C⋆-subalgebra of `Q^ω`. -/
theorem TracialEmbedding.hom_injective {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A) {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    {ω : Ultrafilter ℕ} (E : TracialEmbedding (fun a : A => τ a) X ω) :
    Function.Injective E.hom := by
  refine StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving
    (tauA := τ) (tauB := TracialUltraproduct.ultratraceFaithfulTracialState X ω)
    (pi := E.hom) ?_
  intro a
  exact E.trace a

end

end GroupApproximation.Full.TWWSchafhauser
