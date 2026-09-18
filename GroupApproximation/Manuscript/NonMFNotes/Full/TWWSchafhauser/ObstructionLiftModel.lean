import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Analysis.FilterMatrixCStarCorona

/-!
# The last step of Schafhauser's argument: a lift into `∏_ω M_k` is a quasidiagonal trace

Lane `TWWSchafhauser-3d` (work order `WO-TWWCore-3`, piece 3d).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), which
cites Tikuisis--White--Winter, *Quasidiagonality of nuclear C⋆-algebras*,
Ann. of Math. (2) **185** (2017), Theorem A, through the new proof of
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*,
J. reine angew. Math. **759** (2020), 291--304.

Schafhauser's proof ends as follows (§5 of the Crelle paper).  Once the class of
the trace-kernel extension vanishes, the tracial embedding `A → ∏^ω M_{k_n}`
lifts, up to unitary equivalence, to a unital `⋆`-homomorphism
`ψ : A → ∏_ω M_{k_n} = ℓ∞(M_{k_n}) / c_ω(M_{k_n})` into the **norm** ultraproduct.
Because `A` is nuclear, `ψ` has a unital completely positive lift
`A → ℓ∞(M_{k_n})` (Choi--Effros), whose coordinates are ucp maps
`φ_n : A → M_{k_n}`; and since the unitary conjugation does not change traces,
`tr φ_n(a) → τ(a)` along `ω`.  The theorem follows from this.

This file proves that final passage, unconditionally:

* `FilterTraceModel τ l` --- ucp matrix models whose multiplicative and trace
  defects are null **along an arbitrary filter** `l` (in the application, a free
  ultrafilter);
* `FilterTraceModel.isLocallyQuasidiagonalTrace` --- at a `NeBot` filter such
  models give the local (finite-set/`ε`) form of quasidiagonality: finitely many
  `l`-null defects are simultaneously small on an `l`-large, hence nonempty, set;
* `FilterTraceModel.isQuasidiagonalTrace` --- on a separable algebra the local form
  upgrades to `Quasidiagonal.IsQuasidiagonalTrace`
  (`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`, proved);
* `CoronaLiftModel τ space l` --- the form the lifting step produces: a unital
  `⋆`-homomorphism `A →⋆ₐ[ℂ] FilterMatrixCStarCorona` together with a ucp lift
  and the trace condition;
* `CoronaLiftModel.toFilterTraceModel`, `isQuasidiagonalTrace_of_coronaLiftModel`
  --- multiplicativity of `ψ` in the norm ultraproduct is exactly `l`-nullity of the
  multiplicative defects of the lift (`filterMatrixCStarCoronaMk_eq_iff`).

Nothing here is assumed: there is no input structure and no hypothesis standing
in for a literature theorem.  The consumer is `Full/TWWSchafhauser/Assembly.lean`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Matrix GroupApproximation.Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## Matrix models along a filter -/

/-- **Quasidiagonal matrix models along a filter `l`.**  Field for field this is
`Quasidiagonal.QuasidiagonalTraceModel`, except that the two defects are null
along `l` rather than along `atTop`.  At a free ultrafilter `ω` this is what a
`⋆`-homomorphism into the norm ultraproduct `∏_ω M_{k_n}` with a ucp lift and a
compatible trace amounts to (Schafhauser, Crelle 759 (2020), §5). -/
structure FilterTraceModel (τ : A → ℂ) (l : Filter ℕ) where
  /-- The finite matrix sizes. -/
  space : ℕ → FiniteModel
  /-- The maps `φ_n : A → M_{k_n}`. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φ_n` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φ_n` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- Multiplicativity along `l`, in operator norm. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) l (nhds 0)
  /-- The normalized traces converge to `τ` along `l`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) l (nhds 0)

/-- **Models along a nontrivial filter give a locally quasidiagonal trace.**

For a finite `F` and `ε > 0`, the `|F|²` multiplicative defects and the `|F|`
trace defects are each eventually `≤ ε` along `l`; finitely many eventualities
hold together, and an `l`-eventual property has a witness because `l` is
`NeBot`. -/
theorem FilterTraceModel.isLocallyQuasidiagonalTrace {τ : A → ℂ} {l : Filter ℕ}
    [l.NeBot] (M : FilterTraceModel τ l) : IsLocallyQuasidiagonalTrace τ := by
  intro F ε hε
  have hmul : ∀ᶠ n in l, ∀ x ∈ F, ∀ y ∈ F,
      ‖M.map n (x * y) - M.map n x * M.map n y‖ ≤ ε := by
    refine (Filter.eventually_all_finset F).2 fun x _ ↦ ?_
    refine (Filter.eventually_all_finset F).2 fun y _ ↦ ?_
    filter_upwards [TracialUltraproduct.eventually_lt_of_tendsto_zero
      (M.tendsto_mul x y) hε] with n hn
    exact hn.le
  have htr : ∀ᶠ n in l, ∀ x ∈ F,
      ‖τ x - normTrace (M.space n) (M.map n x)‖ ≤ ε := by
    refine (Filter.eventually_all_finset F).2 fun x _ ↦ ?_
    filter_upwards [TracialUltraproduct.eventually_lt_of_tendsto_zero
      (M.tendsto_trace x) hε] with n hn
    exact hn.le
  obtain ⟨n, hn₁, hn₂⟩ := (hmul.and htr).exists
  exact ⟨M.space n, M.map n, M.map_one n, M.completelyPositive n, hn₁, hn₂⟩

/-- **Models along a nontrivial filter give a quasidiagonal trace**, on a separable
algebra.  The diagonal argument is
`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`. -/
theorem FilterTraceModel.isQuasidiagonalTrace {τ : A → ℂ} {l : Filter ℕ}
    [l.NeBot] (hsep : TopologicalSpace.SeparableSpace A)
    (M : FilterTraceModel τ l) : IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep
    M.isLocallyQuasidiagonalTrace

/-! ## A `⋆`-homomorphism into the norm ultraproduct, with a ucp lift -/

/-- **A lifted corona homomorphism**: a unital `⋆`-homomorphism
`ψ : A → ℓ∞(M_{k_n}) / c_l(M_{k_n})` together with a lift by unital completely
positive maps `φ_n : A → M_{k_n}` and the trace condition `tr φ_n(a) → τ(a)`
along `l`.

This is the output of the lifting step of Schafhauser's argument (Crelle 759
(2020), Theorem 5.1 and its proof) at `l = ω`: the vanishing obstruction gives
`ψ`, nuclearity gives the ucp lift (Choi--Effros), and the trace condition is the
statement that `ψ` induces `τ` under the limit trace. -/
structure CoronaLiftModel (τ : A → ℂ) (space : ℕ → FiniteModel)
    [∀ n, Nonempty (space n)] (l : Filter ℕ) where
  /-- The unital `⋆`-homomorphism into the norm corona at `l`. -/
  hom : A →⋆ₐ[ℂ] FilterMatrixCStarCorona (fun n ↦ (space n).carrier) l
  /-- The coordinates of the lift, `φ_n : A → M_{k_n}`. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φ_n` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φ_n` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- The lift, as a bounded sequence. -/
  seq : A → BoundedMatrixSequence (fun n ↦ (space n).carrier)
  /-- The lift has the `φ_n` as coordinates. -/
  seq_apply : ∀ (a : A) (n : ℕ), seq a n = map n a
  /-- The lift lifts `ψ`. -/
  mk_seq : ∀ a : A,
    filterMatrixCStarCoronaMk (fun n ↦ (space n).carrier) l (seq a) = hom a
  /-- The normalized traces of the lift converge to `τ` along `l`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) l (nhds 0)

/-- **Multiplicativity in the norm ultraproduct is asymptotic multiplicativity
of the lift.**  Since `ψ` is multiplicative, the lifts of `ab` and of `a · b`
have the same class, so their difference is `l`-null
(`filterMatrixCStarCoronaMk_eq_iff`), and its coordinates are the defects. -/
theorem CoronaLiftModel.tendsto_mul {τ : A → ℂ} {space : ℕ → FiniteModel}
    [∀ n, Nonempty (space n)] {l : Filter ℕ} (M : CoronaLiftModel τ space l)
    (a b : A) :
    Tendsto (fun n ↦ ‖M.map n (a * b) - M.map n a * M.map n b‖) l (nhds 0) := by
  have hclass : filterMatrixCStarCoronaMk (fun n ↦ (space n).carrier) l
        (M.seq (a * b))
      = filterMatrixCStarCoronaMk (fun n ↦ (space n).carrier) l
        (M.seq a * M.seq b) := by
    rw [map_mul, M.mk_seq, M.mk_seq, M.mk_seq, map_mul]
  have hnull := (filterMatrixCStarCoronaMk_eq_iff _ _ _ _).1 hclass
  have hseq : Tendsto (fun n ↦ ‖(M.seq (a * b) - M.seq a * M.seq b) n‖) l
      (nhds 0) := hnull
  refine hseq.congr fun n ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply,
    M.seq_apply, M.seq_apply, M.seq_apply]

/-- A lifted corona homomorphism is a family of models along `l`. -/
def CoronaLiftModel.toFilterTraceModel {τ : A → ℂ} {space : ℕ → FiniteModel}
    [∀ n, Nonempty (space n)] {l : Filter ℕ} (M : CoronaLiftModel τ space l) :
    FilterTraceModel τ l where
  space := space
  map := M.map
  map_one := M.map_one
  completelyPositive := M.completelyPositive
  tendsto_mul := M.tendsto_mul
  tendsto_trace := M.tendsto_trace

/-- **The final passage of Schafhauser's proof.**  On a separable C⋆-algebra, a
unital `⋆`-homomorphism into the norm ultraproduct `∏_l M_{k_n}` (at a `NeBot`
filter) with a ucp lift inducing `τ` makes `τ` quasidiagonal. -/
theorem isQuasidiagonalTrace_of_coronaLiftModel {τ : A → ℂ}
    {space : ℕ → FiniteModel} [∀ n, Nonempty (space n)] {l : Filter ℕ} [l.NeBot]
    (hsep : TopologicalSpace.SeparableSpace A) (M : CoronaLiftModel τ space l) :
    IsQuasidiagonalTrace τ :=
  M.toFilterTraceModel.isQuasidiagonalTrace hsep

/-- The existential form, the shape in which the lifting step is consumed by
`Full/TWWSchafhauser/Assembly.lean`. -/
def HasCoronaLiftModel (τ : A → ℂ) : Prop :=
  ∃ (space : ℕ → FiniteModel) (_ : ∀ n, Nonempty (space n)) (ω : Ultrafilter ℕ),
    Nonempty (CoronaLiftModel τ space (ω : Filter ℕ))

/-- **A separable algebra whose trace has a lifted corona homomorphism at some
ultrafilter has a quasidiagonal trace.**  (An ultrafilter is `NeBot`.) -/
theorem isQuasidiagonalTrace_of_hasCoronaLiftModel {τ : A → ℂ}
    (hsep : TopologicalSpace.SeparableSpace A) (h : HasCoronaLiftModel τ) :
    IsQuasidiagonalTrace τ := by
  obtain ⟨space, hne, ω, ⟨M⟩⟩ := h
  exact @isQuasidiagonalTrace_of_coronaLiftModel A _ τ space hne (ω : Filter ℕ)
    (Ultrafilter.neBot ω) hsep M

end

end GroupApproximation.Full.TWWSchafhauser
