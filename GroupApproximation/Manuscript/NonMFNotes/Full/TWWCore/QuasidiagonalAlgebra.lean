import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXImpliesIX

/-!
# Quasidiagonal C⋆-algebras, and Brown's step from a faithful quasidiagonal trace

Lane TWWCore (work order WO-NM16-2).  In the Related-work paragraph of
`non_mf_groups_exist.tex` (L315--318), Tikuisis, White and Winter answer the
Blackadar--Kirchberg question on quasidiagonality for UCT algebras with a
faithful trace.  Their theorem, recalled at L279--281, is about *traces*.  The
question asks about *algebras*.  This file supplies the step between the two.

* `QuasidiagonalAlgebraModel A` is Voiculescu's abstract characterization of
  quasidiagonality for a unital C⋆-algebra (Brown--Ozawa, *C⋆-algebras and
  finite-dimensional approximations*, §7.1).  It consists of unital completely
  positive maps `φₙ : A → M_{kₙ}` that are asymptotically multiplicative and
  asymptotically isometric, `‖φₙ(a)‖ → ‖a‖`.  `IsQuasidiagonalCStarAlgebra A`
  also asks that `A` be separable.  Empty model spaces are allowed, so the
  zero algebra is quasidiagonal.
* `isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace` is Brown's
  argument (N. Brown, *Invariant means and finite representation theory of
  C⋆-algebras*, Mem. AMS 184 (2006), §3.5).  A
  faithful tracial state with quasidiagonal matrix models makes the algebra
  quasidiagonal:
  - The models define a star homomorphism into the norm-matrix corona
    `∏ M_{kₙ} / ⊕ M_{kₙ}`, whose kernel the faithful trace kills
    (`NinetyNineProblems.coronaHom_injective_of_faithful`).
  - Hence it is isometric (`NonUnitalStarAlgHom.norm_map`), and the corona norm
    is `limsup ‖φₙ(a)‖` (`norm_filterMatrixCorona_mk_eq_limsup`).
  - The same holds along every subsequence.  Since each `φₙ` is contractive
    (`Quasidiagonal.ucp_norm_le`), the limsup is a genuine limit.

The RelatedTWW vocabulary of the other swarm is restated here, not imported;
its modules are WIP snapshots.
-/

namespace GroupApproximation.Full.TWWCore

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## Quasidiagonal C⋆-algebras -/

/-- **Quasidiagonal matrix models** of a unital C⋆-algebra `A`
(Voiculescu; Brown--Ozawa §7.1): unital completely positive maps
`φₙ : A → M_{kₙ}`, asymptotically multiplicative in operator norm and
asymptotically isometric.  This is the vocabulary of `non_mf_groups_exist.tex`
L315--318. -/
structure QuasidiagonalAlgebraModel (A : Type u) [CStarAlgebra A] where
  /-- The finite matrix sizes `kₙ`. -/
  space : ℕ → FiniteModel
  /-- The maps `φₙ : A → M_{kₙ}`, genuinely `ℂ`-linear. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φₙ` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φₙ` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    Quasidiagonal.IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- Asymptotic multiplicativity in operator norm. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  /-- Asymptotic isometry: `‖φₙ(a)‖ → ‖a‖`. -/
  tendsto_norm : ∀ a : A, Tendsto (fun n ↦ ‖map n a‖) atTop (nhds ‖a‖)

/-- **Quasidiagonality of a separable unital C⋆-algebra** (`non_mf_groups_exist.tex`
L315--318): `A` is separable and has quasidiagonal matrix models. -/
def IsQuasidiagonalCStarAlgebra (A : Type u) [CStarAlgebra A] : Prop :=
  TopologicalSpace.SeparableSpace A ∧ Nonempty (QuasidiagonalAlgebraModel A)

/-! ## Reindexing trace models -/

/-- Reindex a quasidiagonal trace model along a sequence tending to infinity.
Every clause is a limit along `atTop`, so each survives composition. -/
def reindexTraceModel {A : Type u} [CStarAlgebra A] {τ : A → ℂ}
    (M : Quasidiagonal.QuasidiagonalTraceModel τ) (s : ℕ → ℕ)
    (hs : Tendsto s atTop atTop) : Quasidiagonal.QuasidiagonalTraceModel τ where
  space n := M.space (s n)
  map n := M.map (s n)
  map_one n := M.map_one (s n)
  completelyPositive n := M.completelyPositive (s n)
  tendsto_mul a b := (M.tendsto_mul a b).comp hs
  tendsto_trace a := (M.tendsto_trace a).comp hs

/-- A trace model of a unital trace has a tail all of whose spaces are
nonempty.  An empty model reports normalized trace `0` at the unit, and
`MFTraceModel.eventually_card_pos` shows this happens only finitely often. -/
theorem exists_nonempty_traceModel {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A)
    (M : Quasidiagonal.QuasidiagonalTraceModel (fun a : A ↦ τ a)) :
    ∃ M' : Quasidiagonal.QuasidiagonalTraceModel (fun a : A ↦ τ a),
      ∀ n, Nonempty (M'.space n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((M.toMFTraceModel Quasidiagonal.ucpContractive).eventually_card_pos
      τ.apply_one)
  refine ⟨reindexTraceModel M (fun n ↦ n + N) (tendsto_add_atTop_nat N),
    fun n ↦ ?_⟩
  exact Fintype.card_pos_iff.mp (hN (n + N) (Nat.le_add_left N n))

/-! ## Brown's argument -/

/-- **Norm recovery through the corona.**  For an MF model of a faithful
tracial state with nonempty spaces, `limsup ‖φₙ(a)‖ = ‖a‖`.  The corona
homomorphism is injective (`coronaHom_injective_of_faithful`), hence
isometric, and the corona norm is the limsup of the coordinate norms. -/
theorem limsup_norm_mfTraceModel_eq {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A)
    (N : ShulmanTrace.MFTraceModel (fun a : A ↦ τ a))
    [∀ n, Nonempty (N.space n)] (a : A) :
    limsup (fun n ↦ ‖N.map n a‖) atTop = ‖a‖ := by
  have hiso : ‖N.coronaHom a‖ = ‖a‖ :=
    NonUnitalStarAlgHom.norm_map N.coronaHom
      (NinetyNineProblems.coronaHom_injective_of_faithful τ N) a
  have hform : ‖N.coronaHom a‖ = limsup (fun n ↦ ‖N.map n a‖) atTop := by
    change ‖Ideal.Quotient.mk
        (nullMatrixSequenceIdeal (fun n ↦ N.space n) cofinite) (N.seq a)‖ = _
    simpa only [ShulmanTrace.MFTraceModel.seq_apply, Nat.cofinite_eq_atTop] using
      norm_filterMatrixCorona_mk_eq_limsup (fun n ↦ N.space n) cofinite (N.seq a)
  exact hform.symm.trans hiso

/-- Norm recovery for a quasidiagonal trace model of a faithful trace with
nonempty spaces, as a limsup. -/
theorem limsup_norm_traceModel_eq {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A)
    (M : Quasidiagonal.QuasidiagonalTraceModel (fun a : A ↦ τ a))
    (hne : ∀ n, Nonempty (M.space n)) (a : A) :
    limsup (fun n ↦ ‖M.map n a‖) atTop = ‖a‖ := by
  haveI : ∀ n,
      Nonempty ((M.toMFTraceModel Quasidiagonal.ucpContractive).space n) := hne
  exact limsup_norm_mfTraceModel_eq τ
    (M.toMFTraceModel Quasidiagonal.ucpContractive) a

/-- **The limsup is a limit.**  Each `φₙ` is a unital completely positive
contraction, so `‖φₙ(a)‖ ≤ ‖a‖`.  If `‖φₙ(a)‖ ≤ b < ‖a‖` held frequently,
the subsequence where it holds would be a trace model with limsup `≤ b`,
contradicting `limsup_norm_traceModel_eq`. -/
theorem tendsto_norm_traceModel {A : Type u} [CStarAlgebra A]
    (τ : FaithfulTracialState A)
    (M : Quasidiagonal.QuasidiagonalTraceModel (fun a : A ↦ τ a))
    (hne : ∀ n, Nonempty (M.space n)) (a : A) :
    Tendsto (fun n ↦ ‖M.map n a‖) atTop (nhds ‖a‖) := by
  have hle : ∀ n, ‖M.map n a‖ ≤ ‖a‖ := fun n ↦
    Quasidiagonal.ucp_norm_le (M.map n) (M.map_one n) (M.completelyPositive n) a
  refine tendsto_order.2 ⟨fun b hb ↦ ?_,
    fun b hb ↦ Eventually.of_forall fun n ↦ lt_of_le_of_lt (hle n) hb⟩
  by_contra hev
  obtain ⟨s, hs, hsb⟩ := extraction_of_frequently_atTop (not_eventually.mp hev)
  have hst : Tendsto s atTop atTop := StrictMono.tendsto_atTop hs
  have hne' : ∀ n, Nonempty ((reindexTraceModel M s hst).space n) :=
    fun n ↦ hne (s n)
  have heq : limsup (fun n ↦ ‖M.map (s n) a‖) atTop = ‖a‖ :=
    limsup_norm_traceModel_eq τ (reindexTraceModel M s hst) hne' a
  have hbound : limsup (fun n ↦ ‖M.map (s n) a‖) atTop ≤ b :=
    limsup_le_of_le
      (isCoboundedUnder_le_of_le atTop fun n ↦ norm_nonneg (M.map (s n) a))
      (Eventually.of_forall fun n ↦ not_lt.mp (hsb n))
  linarith

/-- **Brown's step: a faithful quasidiagonal trace makes the algebra
quasidiagonal.**  This is the passage from the trace-theoretic theorem of
Tikuisis--White--Winter (`non_mf_groups_exist.tex` L279--281) to the
algebra-level answer of L315--318.  The models of the trace, trimmed to
nonempty spaces, are already quasidiagonal models of the algebra. -/
theorem isQuasidiagonalCStarAlgebra_of_faithful_quasidiagonalTrace
    {A : Type u} [CStarAlgebra A] (hsep : TopologicalSpace.SeparableSpace A)
    (τ : FaithfulTracialState A)
    (hqd : Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)) :
    IsQuasidiagonalCStarAlgebra A := by
  obtain ⟨M⟩ := hqd
  obtain ⟨M', hne⟩ := exists_nonempty_traceModel τ M
  exact ⟨hsep, ⟨{
    space := M'.space
    map := M'.map
    map_one := M'.map_one
    completelyPositive := M'.completelyPositive
    tendsto_mul := M'.tendsto_mul
    tendsto_norm := tendsto_norm_traceModel τ M' hne }⟩⟩

end

end GroupApproximation.Full.TWWCore
