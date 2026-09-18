import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingEndpoint
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ExtensionPullback
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionLiftModel
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionTraceTransfer

/-!
# The trace-kernel extension pulled back along a tracial embedding

Lane TWWSchafhauser-3c (work order WO-TWWCore-3, piece 3c).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378).  The
source is C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*,
J. reine angew. Math. **759** (2020), §3--5.

Fix nonempty finite models `X n`, a free ultrafilter `ω ≤ cofinite`, and a tracial
embedding `E : TracialEmbedding τ X ω` (lane 3b).  Schafhauser's trace-kernel
extension is

  `0 → J → Q_ω → Q^ω → 0`,   `π = traceKernelQuotient X ω hω`,

and its pullback along `E.hom : A → Q^ω` is the C⋆-algebra extension

  `0 → J → P = {(a, x) ∈ A × Q_ω | E.hom a = π x} → A → 0`.

Proved here, with no hypotheses:

* `traceKernelPullback`, `traceKernelPullbackFst_surjective`: `P` is a closed
  star subalgebra of `A × Q_ω` (`ExtensionPullback.lean`), and it is an extension
  of `A`.
* `TracialEmbedding.coronaLift`, `TracialEmbedding.pullbackLinearSplitting`:
  **nuclear liftability.**  The ucp lift of lane 3b gives a linear splitting
  `a ↦ (a, [E.lift a])` of `P → A`.  Its second coordinate is the corona class of
  a sequence of unital completely positive maps.
* `TraceKernelLift E hω`: the output of Schafhauser's lifting step (Crelle 759,
  Theorem 5.1).  It is a unital ⋆-homomorphism `ψ : A → Q_ω` with
  `π ∘ ψ = Ad u ∘ E.hom` for a unitary `u ∈ Q^ω`, together with a ucp lift of `ψ`.
* `TraceKernelLift.toCoronaLiftModel`, `hasCoronaLiftModel_of_traceKernelLift`:
  such a lift is a `CoronaLiftModel τ X ω` (lane 3d), so it makes `τ`
  quasidiagonal.  The trace condition comes from `tr_ω (u x u⋆) = tr_ω x`
  (`ultratrace_conj`), and the corona is moved from `ℓ∞/c₀` to `ℓ∞/c_ω` by
  `normCoronaToFilterCorona` (both from `ObstructionTraceTransfer.lean`, lane 3d1).

The existence of a `TraceKernelLift` is the absorption-plus-obstruction argument of
Schafhauser §4--5 (Elliott--Kucerovsky absorption, then the vanishing of the
`Ext` class).  It is not proved in this file.  The work orders for it are listed
in `fk/status/TWWSchafhauser-3c.md`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

/-! ## The pulled-back trace-kernel extension -/

/-- **The trace-kernel extension pulled back along `θ : A → Q^ω`**
(Schafhauser 2020, §3): `P = {(a, x) ∈ A × Q_ω | θ a = π x}`. -/
def traceKernelPullback {A : Type u} [CStarAlgebra A] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)) :
    StarSubalgebra ℂ (A × NormMatrixCStarCorona (fun n => X n)) :=
  extensionPullback (traceKernelQuotient X ω hω) θ

theorem mem_traceKernelPullback {A : Type u} [CStarAlgebra A] (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ))
    (x : A × NormMatrixCStarCorona (fun n => X n)) :
    x ∈ traceKernelPullback X ω hω θ ↔ θ x.1 = traceKernelQuotient X ω hω x.2 :=
  Iff.rfl

/-- The pulled-back trace-kernel extension is an extension of `A`: the map
`P → A` is onto. -/
theorem traceKernelPullbackFst_surjective {A : Type u} [CStarAlgebra A]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (θ : A →⋆ₐ[ℂ] TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)) :
    Function.Surjective (extensionPullbackFst (traceKernelQuotient X ω hω) θ) :=
  extensionPullbackFst_surjective (traceKernelQuotient X ω hω) θ
    (traceKernelQuotient_surjective X ω hω)

/-! ## Nuclear liftability from the ucp lift of lane 3b -/

/-- The corona class of the ucp lift, `a ↦ [E.lift a] ∈ Q_ω`.  It is linear. -/
def TracialEmbedding.coronaLift {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) : A →ₗ[ℂ] NormMatrixCStarCorona (fun n => X n) :=
  (normMatrixCStarCoronaQuotient (fun n => X n)).toAlgHom.toLinearMap.comp E.lift

theorem TracialEmbedding.coronaLift_apply {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (a : A) :
    E.coronaLift a = normMatrixCStarCoronaMk (fun n => X n) (E.lift a) :=
  rfl

/-- The corona class of the ucp lift lifts `E.hom` through the trace-kernel
quotient. -/
theorem TracialEmbedding.traceKernelQuotient_coronaLift {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (hω : (ω : Filter ℕ) ≤ cofinite) (a : A) :
    traceKernelQuotient X ω hω (E.coronaLift a) = E.hom a :=
  E.traceKernelQuotient_mk_lift hω a

/-- **The pulled-back trace-kernel extension is nuclearly liftable**
(Schafhauser 2020, §3).  The splitting is `a ↦ (a, [E.lift a])`, and its second
coordinate is the class of the sequence of ucp maps `E.map n`. -/
def TracialEmbedding.pullbackLinearSplitting {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (hω : (ω : Filter ℕ) ≤ cofinite) :
    A →ₗ[ℂ] traceKernelPullback X ω hω E.hom :=
  extensionPullbackLinearSplitting (traceKernelQuotient X ω hω) E.hom E.coronaLift
    (E.traceKernelQuotient_coronaLift hω)

theorem TracialEmbedding.fst_pullbackLinearSplitting {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (hω : (ω : Filter ℕ) ≤ cofinite) (a : A) :
    extensionPullbackFst (traceKernelQuotient X ω hω) E.hom
      (E.pullbackLinearSplitting hω a) = a :=
  rfl

theorem TracialEmbedding.snd_pullbackLinearSplitting {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (hω : (ω : Filter ℕ) ≤ cofinite) (a : A) :
    extensionPullbackSnd (traceKernelQuotient X ω hω) E.hom
      (E.pullbackLinearSplitting hω a)
      = normMatrixCStarCoronaMk (fun n => X n) (E.lift a) :=
  rfl

/-! ## The lifting step and its consumer -/

/-- **A lift of the tracial embedding through the trace-kernel extension, up to
unitary equivalence, with a ucp lift** (Schafhauser, Crelle 759 (2020),
Theorem 5.1 and its proof).  It consists of a unital ⋆-homomorphism
`ψ : A → Q_ω` with `π ∘ ψ = Ad u ∘ E.hom` for a unitary `u ∈ Q^ω`, and ucp maps
`φ_n : A → M_{X n}` whose corona class is `ψ`. -/
structure TraceKernelLift {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    (E : TracialEmbedding τ X ω) (hω : (ω : Filter ℕ) ≤ cofinite) where
  /-- The unital ⋆-homomorphism `ψ : A → Q_ω`. -/
  hom : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n)
  /-- The conjugating unitary `u ∈ Q^ω`. -/
  unit : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)
  star_unit_mul : star unit * unit = 1
  unit_mul_star : unit * star unit = 1
  /-- `π ∘ ψ = Ad u ∘ E.hom`. -/
  lifts : ∀ a : A, traceKernelQuotient X ω hω (hom a) = unit * E.hom a * star unit
  /-- The coordinates of the ucp lift of `ψ`. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ
  /-- Each coordinate is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each coordinate is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    Quasidiagonal.IsCompletelyPositiveOnMatrices (X n) ⇑(map n)
  /-- The lift, as a bounded sequence. -/
  seq : A → TracialUltraproduct.ModelBoundedSequence X
  /-- The lift has the `φ_n` as coordinates. -/
  seq_apply : ∀ (a : A) (n : ℕ), seq a n = map n a
  /-- The lift lifts `ψ`. -/
  mk_seq : ∀ a : A, normMatrixCStarCoronaMk (fun n => X n) (seq a) = hom a

/-- **The traces of the ucp lift converge to `τ`.**  The ultratrace of `[seq a]`
is `tr_ω (u E.hom(a) u⋆) = tr_ω (E.hom a) = τ a`. -/
theorem TraceKernelLift.tendsto_trace {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    {E : TracialEmbedding τ X ω} {hω : (ω : Filter ℕ) ≤ cofinite}
    (L : TraceKernelLift E hω) (a : A) :
    Tendsto (fun n => ‖τ a - normTrace (X n) (L.map n a)‖) (ω : Filter ℕ) (nhds 0) := by
  have htr : TracialUltraproduct.seqUltratrace X ω (L.seq a) = τ a := by
    rw [← ultratrace_traceKernelQuotient_mk X ω hω (L.seq a), L.mk_seq a, L.lifts a,
      ultratrace_conj X ω L.star_unit_mul (E.hom a),
      ← TracialUltraproduct.ultratraceCLM_apply]
    exact E.trace a
  have h := tendsto_norm_sub_normTrace X ω (L.seq a)
  rw [htr] at h
  simpa only [L.seq_apply] using h

/-- **A trace-kernel lift is a lifted corona model** (lane 3d).  The
⋆-homomorphism is `ψ` followed by the quotient `Q_ω → ℓ∞/c_ω`, and the ucp lift
and trace condition carry over. -/
def TraceKernelLift.toCoronaLiftModel {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    {E : TracialEmbedding τ X ω} {hω : (ω : Filter ℕ) ≤ cofinite}
    (L : TraceKernelLift E hω) : CoronaLiftModel τ X (ω : Filter ℕ) where
  hom := (normCoronaToFilterCorona X (ω : Filter ℕ) hω).comp L.hom
  map := L.map
  map_one := L.map_one
  completelyPositive := L.completelyPositive
  seq := L.seq
  seq_apply := L.seq_apply
  mk_seq a := (normCoronaToFilterCorona_mk X (ω : Filter ℕ) hω (L.seq a)).symm.trans
    (congrArg (normCoronaToFilterCorona X (ω : Filter ℕ) hω) (L.mk_seq a))
  tendsto_trace := L.tendsto_trace

/-- **A trace-kernel lift makes `τ` have a lifted corona model**, hence, on a
separable algebra, a quasidiagonal trace (`isQuasidiagonalTrace_of_hasCoronaLiftModel`). -/
theorem hasCoronaLiftModel_of_traceKernelLift {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} {X : ℕ → FiniteModel} [hX : ∀ n, Nonempty (X n)] {ω : Ultrafilter ℕ}
    {E : TracialEmbedding τ X ω} {hω : (ω : Filter ℕ) ≤ cofinite}
    (L : TraceKernelLift E hω) : HasCoronaLiftModel τ :=
  ⟨X, hX, ω, ⟨L.toCoronaLiftModel⟩⟩

/-- **The lifting step, in existential form.**  Some tracial embedding of `τ` has a
trace-kernel lift. -/
def HasTraceKernelLift {A : Type u} [CStarAlgebra A] (τ : A → ℂ) : Prop :=
  ∃ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (E : @TracialEmbedding A _ τ X hne ω),
    Nonempty (@TraceKernelLift A _ τ X hne ω E hω)

theorem hasCoronaLiftModel_of_hasTraceKernelLift {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} (h : HasTraceKernelLift τ) : HasCoronaLiftModel τ := by
  obtain ⟨X, hne, ω, hω, E, ⟨L⟩⟩ := h
  exact @hasCoronaLiftModel_of_traceKernelLift A _ τ X hne ω E hω L

/-- On a separable algebra, a trace with a trace-kernel lift is quasidiagonal. -/
theorem isQuasidiagonalTrace_of_hasTraceKernelLift {A : Type u} [CStarAlgebra A]
    {τ : A → ℂ} (hsep : TopologicalSpace.SeparableSpace A) (h : HasTraceKernelLift τ) :
    Quasidiagonal.IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_of_hasCoronaLiftModel hsep (hasCoronaLiftModel_of_hasTraceKernelLift h)

end

end GroupApproximation.Full.TWWSchafhauser
