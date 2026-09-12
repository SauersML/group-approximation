import GroupApproximation.Analysis.MFAlgebra
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Sofic.NormMFUniversalQuotient
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Sofic.WeakMFRegularTrace
import Mathlib.GroupTheory.Index

/-!
# The meanings of “MF group”

The phrase “MF group” occurs with several distinct meanings.  This file gives
each meaning a separate Lean name.  It proves the unconditional equivalences
between the group-corona, matrix-ultraproduct, finite-set, and ambient-algebra
formulations, and records the valid one-way implications from the stronger
trace-preserving, trace-regular, reduced-C-star, and supplied full-C-star
formulations.

`IsModularByFiniteMF` is deliberately kept separate: its letters stand for
“modular-by-finite” and it is an unrelated subgroup-lattice property.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## Equivalent group approximation formulations -/

/-- Group-theoretic MF: a faithful homomorphism into the unitary group of a
cofinite norm-matrix corona. -/
def IsGroupTheoreticMF (G : Type u) [Group G] : Prop :=
  IsOperatorMF G

/-- Ultraproduct MF: a faithful homomorphism into an operator-norm matrix
ultraproduct over a free ultrafilter on `ℕ`. -/
def IsUltraproductMF (G : Type u) [Group G] : Prop :=
  ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.cofinite ∧
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : G →* UniversalWeakMF U X, Function.Injective rho

/-- Finite-set MF: every finite part of the multiplication table has an
arbitrarily multiplicative unitary matrix model with normalized separation
constant `1`. -/
def IsFiniteSetMF (G : Type u) [Group G] : Prop :=
  IsNormApproximable G 1

theorem isGroupTheoreticMF_iff_isOperatorMF :
    IsGroupTheoreticMF G ↔ IsOperatorMF G :=
  Iff.rfl

theorem isFiniteSetMF_iff_isGroupTheoreticMF [Countable G] :
    IsFiniteSetMF G ↔ IsGroupTheoreticMF G := by
  exact OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.symm

theorem IsGroupTheoreticMF.isUltraproductMF [Countable G]
    (h : IsGroupTheoreticMF G) : IsUltraproductMF G := by
  have hlocal : IsNormApproximable G 1 :=
    OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mp h
  obtain ⟨A, rho, hrho⟩ :=
    exists_normUltraproductEmbedding_of_isWeakMF
      (show IsWeakMF G from ⟨1, by norm_num, hlocal⟩)
  exact ⟨Ultrafilter.of Filter.cofinite, Ultrafilter.of_le _, A.model,
    A.modelNonempty, rho, hrho⟩

theorem IsUltraproductMF.isGroupTheoreticMF [Countable G]
    (h : IsUltraproductMF G) : IsGroupTheoreticMF G := by
  rcases h with ⟨U, _hU, X, _hX, rho, hrho⟩
  apply (isOperatorMF_iff_normMFResidual_eq_bot (G := G)).mpr
  apply Subgroup.eq_bot_iff_forall (normMFResidual G) |>.2
  intro g hg
  have hker : rho g = 1 :=
    MonoidHom.mem_ker.mp (normMFResidual_le_ultraproduct_ker U X rho hg)
  exact hrho (by simpa using hker)

theorem isUltraproductMF_iff_isGroupTheoreticMF [Countable G] :
    IsUltraproductMF G ↔ IsGroupTheoreticMF G :=
  ⟨IsUltraproductMF.isGroupTheoreticMF,
    IsGroupTheoreticMF.isUltraproductMF⟩

theorem hasMFAlgebraUnitaryEmbedding_iff_isGroupTheoreticMF [Countable G] :
    HasMFAlgebraUnitaryEmbedding G ↔ IsGroupTheoreticMF G :=
  hasMFAlgebraUnitaryEmbedding_iff_isOperatorMF G

/-- The group-corona, ultraproduct, finite-set, and bare-MF-ambient
formulations hold simultaneously exactly when any one of them holds. -/
theorem standardMFDefinitions_iff [Countable G] :
    IsGroupTheoreticMF G ↔
      IsCDEOperatorMF G ∧ IsUltraproductMF G ∧ IsFiniteSetMF G ∧
        HasMFAlgebraUnitaryEmbedding G := by
  constructor
  · intro h
    exact ⟨(isCDEOperatorMF_iff_isOperatorMF G).mpr h,
      h.isUltraproductMF,
      isFiniteSetMF_iff_isGroupTheoreticMF.mpr h,
      hasMFAlgebraUnitaryEmbedding_iff_isGroupTheoreticMF.mpr h⟩
  · rintro ⟨_hcde, _hultra, hfinite, _halgebra⟩
    exact isFiniteSetMF_iff_isGroupTheoreticMF.mp hfinite

/-! ## Trace-preserving and trace-regular MF -/

/-- The regular character, equal to `1` at the identity and `0` elsewhere. -/
noncomputable def regularCharacter (g : G) : ℂ :=
  by
    classical
    exact if g = 1 then 1 else 0

/-- A sequential operator-norm MF approximation whose normalized matrix
traces converge to the regular character of the group. -/
structure TracePreservingMFApproximation (G : Type u) [Group G]
    extends WeakMFApproximation G where
  traceConverges : ∀ g : G,
    Tendsto
      (fun n ↦ normTrace (model n)
        (map n g : Matrix (model n) (model n) ℂ))
      Filter.atTop
      (nhds (regularCharacter g))

/-- Trace-preserving MF: existence of a sequential operator-norm MF model
whose limiting character is the regular character. -/
def IsTracePreservingMF (G : Type u) [Group G] : Prop :=
  Nonempty (TracePreservingMFApproximation G)

/-- Evaluate a finitely supported complex group-ring element in one matrix
stage. -/
noncomputable def matrixGroupRingEvaluation
    (X : ℕ → FiniteModel)
    (phi : ∀ n, G → Matrix.unitaryGroup (X n) ℂ)
    (n : ℕ) : (G →₀ ℂ) →ₗ[ℂ] Matrix (X n) (X n) ℂ :=
  Finsupp.linearCombination ℂ fun g ↦
    (phi n g : Matrix (X n) (X n) ℂ)

/-- Evaluate the algebraic complex group ring in the reduced group C-star
algebra through the left regular representation. -/
noncomputable def reducedGroupRingEvaluation :
    (G →₀ ℂ) →ₗ[ℂ] ReducedGroupCStarTrace.ReducedGroupCStar G :=
  Finsupp.linearCombination ℂ fun g ↦
    reducedLeftRegular G g

/-- Distinct left-regular unitaries are uniformly separated in reduced
operator norm.  The lower bound `1` follows by applying their difference to
the identity point mass and evaluating the `g` coordinate. -/
theorem one_le_norm_reducedGroupRingEvaluation_single_sub
    (g h : G) (hgh : g ≠ h) :
    1 ≤ ‖reducedGroupRingEvaluation (G := G)
      (Finsupp.single g 1 - Finsupp.single h 1)‖ := by
  let T : ReducedGroupCStarTrace.ReducedGroupCStar G :=
    reducedGroupRingEvaluation (G := G)
      (Finsupp.single g 1 - Finsupp.single h 1)
  have hT : T = reducedLeftRegular G g - reducedLeftRegular G h := by
    simp [T, reducedGroupRingEvaluation]
  have hdelta : ‖ReducedGroupCStarTrace.deltaOne G‖ = 1 := by
    classical
    rw [ReducedGroupCStarTrace.deltaOne,
      lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    simp
  have hcoord :
      (((T : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
          ReducedGroupCStarTrace.GroupHilbert G)
        (ReducedGroupCStarTrace.deltaOne G)) g) = 1 := by
    rw [hT]
    change
      ((reducedLeftRegular G g : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
          ReducedGroupCStarTrace.GroupHilbert G) -
        (reducedLeftRegular G h : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
          ReducedGroupCStarTrace.GroupHilbert G))
          (ReducedGroupCStarTrace.deltaOne G) g = 1
    rw [_root_.sub_apply,
      reducedLeftRegular_deltaOne, reducedLeftRegular_deltaOne]
    simp [hgh]
  have hpoint :
      1 ≤ ‖(T : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
          ReducedGroupCStarTrace.GroupHilbert G)
        (ReducedGroupCStarTrace.deltaOne G)‖ := by
    calc
      1 = ‖(((T : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
          ReducedGroupCStarTrace.GroupHilbert G)
        (ReducedGroupCStarTrace.deltaOne G)) g)‖ := by simp [hcoord]
      _ ≤ _ := lp.norm_apply_le_norm (by norm_num) _ g
  have hop := (T : ReducedGroupCStarTrace.GroupHilbert G →L[ℂ]
    ReducedGroupCStarTrace.GroupHilbert G).le_opNorm
      (ReducedGroupCStarTrace.deltaOne G)
  rw [hdelta, mul_one] at hop
  exact hpoint.trans hop

/-- Strong MF in the reduced-norm sense used in the manuscript: a sequence
of positive-dimensional unitary models that is asymptotically multiplicative
in operator norm and recovers the reduced norm of every algebraic group-ring
element.  No trace-convergence premise is added. -/
structure StrongMFApproximation (G : Type u) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  map : ∀ n, G → Matrix.unitaryGroup (model n) ℂ
  asymptoticallyMultiplicative : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(map n (g * h) : Matrix (model n) (model n) ℂ) -
        (map n g : Matrix (model n) (model n) ℂ) * map n h‖ ≤ ε
  reducedNormConverges : ∀ c : G →₀ ℂ,
    Tendsto
      (fun n ↦ ‖matrixGroupRingEvaluation model map n c‖)
      Filter.atTop
      (nhds ‖reducedGroupRingEvaluation (G := G) c‖)

/-- Strong MF, with exactly reduced-norm convergence and no separately
assumed trace convergence. -/
def IsStrongMF (G : Type u) [Group G] : Prop :=
  Nonempty (StrongMFApproximation G)

namespace StrongMFApproximation

/-- Reduced-norm convergence supplies the uniform point separation omitted
from the definition of strong MF, so every strong model is a weak/operator-
corona MF model. -/
noncomputable def toWeakMFApproximation
    (A : StrongMFApproximation G) : WeakMFApproximation G where
  separation := 1 / 2
  separation_pos := by norm_num
  model := A.model
  modelNonempty := A.modelNonempty
  map := A.map
  asymptoticallyMultiplicative := A.asymptoticallyMultiplicative
  separatedEventually := by
    intro g h hgh
    let c : G →₀ ℂ := Finsupp.single g 1 - Finsupp.single h 1
    have htarget : 1 ≤ ‖reducedGroupRingEvaluation (G := G) c‖ := by
      exact one_le_norm_reducedGroupRingEvaluation_single_sub g h hgh
    have hev : ∀ᶠ n in Filter.atTop,
        dist (‖matrixGroupRingEvaluation A.model A.map n c‖)
          ‖reducedGroupRingEvaluation (G := G) c‖ < 1 / 2 :=
      (Metric.tendsto_nhds.mp (A.reducedNormConverges c))
        (1 / 2) (by norm_num)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn ↦ ?_⟩
    have hdist := hN n hn
    rw [Real.dist_eq] at hdist
    have heval :
        matrixGroupRingEvaluation A.model A.map n c =
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n h := by
      simp [c, matrixGroupRingEvaluation]
    rw [heval] at hdist
    have hlower := (abs_lt.mp hdist).1
    linarith

end StrongMFApproximation

/-- Strong MF implies the operator-norm ultraproduct formulation without a
countability assumption. -/
theorem IsStrongMF.isUltraproductMF
    (h : IsStrongMF G) : IsUltraproductMF G := by
  rcases h with ⟨A⟩
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hU : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le _
  obtain ⟨rho, hrho⟩ := A.toWeakMFApproximation.exists_normUltraproductEmbedding hU
  exact ⟨U, hU, A.model, A.modelNonempty, rho, hrho⟩

/-- Strong MF implies the standard group-theoretic MF property for countable groups. -/
theorem IsStrongMF.isGroupTheoreticMF [Countable G]
    (h : IsStrongMF G) : IsGroupTheoreticMF G :=
  h.isUltraproductMF.isGroupTheoreticMF

/-- A trace-regular MF approximation is trace-preserving and, in addition,
recovers the reduced operator norm of every algebraic group-ring element.
This is deliberately not named `StrongMFApproximation`: the manuscript's
strong-MF definition requires reduced-norm convergence but does not separately
assume trace convergence. -/
structure TraceRegularMFApproximation (G : Type u) [Group G]
    extends TracePreservingMFApproximation G where
  reducedNormConverges : ∀ c : G →₀ ℂ,
    Tendsto
      (fun n ↦ ‖matrixGroupRingEvaluation model map n c‖)
      Filter.atTop
      (nhds ‖reducedGroupRingEvaluation (G := G) c‖)

/-- Existence of a trace-preserving, reduced-norm-preserving MF
approximation.  This property is stronger on its face than the manuscript's
strong-MF predicate. -/
def IsTraceRegularMF (G : Type u) [Group G] : Prop :=
  Nonempty (TraceRegularMFApproximation G)

theorem IsTraceRegularMF.isTracePreservingMF
    (h : IsTraceRegularMF G) : IsTracePreservingMF G := by
  rcases h with ⟨A⟩
  exact ⟨A.toTracePreservingMFApproximation⟩

theorem IsTracePreservingMF.isUltraproductMF
    (h : IsTracePreservingMF G) : IsUltraproductMF G := by
  rcases h with ⟨A⟩
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hU : ((U : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le _
  obtain ⟨rho, hrho⟩ :=
    A.toWeakMFApproximation.exists_normUltraproductEmbedding hU
  exact ⟨U, hU, A.model, A.modelNonempty, rho, hrho⟩

theorem IsTracePreservingMF.isGroupTheoreticMF [Countable G]
    (h : IsTracePreservingMF G) : IsGroupTheoreticMF G :=
  h.isUltraproductMF.isGroupTheoreticMF

theorem IsTraceRegularMF.isGroupTheoreticMF [Countable G]
    (h : IsTraceRegularMF G) : IsGroupTheoreticMF G :=
  h.isTracePreservingMF.isGroupTheoreticMF

/-! ## Reduced group C-star algebra formulation -/

/-- Reduced-C-star MF: the concrete reduced group C-star algebra is an MF
C-star algebra. -/
def IsReducedGroupCStarMF (G : Type u) [Group G] : Prop :=
  IsMFAlgebra (ReducedGroupCStarTrace.ReducedGroupCStar G)

/-- The bare MF embedding property of the concrete reduced group C-star
algebra already forces the group-theoretic MF property.  Separability is not
used in this implication. -/
theorem reducedGroupCStar_isGroupTheoreticMF_of_hasMFEmbedding [Countable G]
    (h : HasMFEmbedding (ReducedGroupCStarTrace.ReducedGroupCStar G)) :
    IsGroupTheoreticMF G :=
  h.isOperatorMF
    (reducedLeftRegularUnitaryHom G)
    (reducedLeftRegularUnitaryHom_injective G)

theorem IsReducedGroupCStarMF.isGroupTheoreticMF [Countable G]
    (h : IsReducedGroupCStarMF G) : IsGroupTheoreticMF G := by
  exact reducedGroupCStar_isGroupTheoreticMF_of_hasMFEmbedding h.2

/-! ## Contrapositive obstruction package -/

theorem not_isCDEOperatorMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsCDEOperatorMF G := by
  simpa [IsGroupTheoreticMF] using
    (mt (isCDEOperatorMF_iff_isOperatorMF G).mp h)

theorem not_isUltraproductMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsUltraproductMF G :=
  mt IsUltraproductMF.isGroupTheoreticMF h

theorem not_isFiniteSetMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsFiniteSetMF G :=
  mt isFiniteSetMF_iff_isGroupTheoreticMF.mp h

theorem not_hasMFAlgebraUnitaryEmbedding_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ HasMFAlgebraUnitaryEmbedding G :=
  mt hasMFAlgebraUnitaryEmbedding_iff_isGroupTheoreticMF.mp h

theorem not_isTracePreservingMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsTracePreservingMF G :=
  mt IsTracePreservingMF.isGroupTheoreticMF h

theorem not_isStrongMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsStrongMF G :=
  mt IsStrongMF.isGroupTheoreticMF h

theorem not_isTraceRegularMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsTraceRegularMF G :=
  mt IsTraceRegularMF.isGroupTheoreticMF h

theorem not_isReducedGroupCStarMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsReducedGroupCStarMF G :=
  mt IsReducedGroupCStarMF.isGroupTheoreticMF h

/-- A non-MF group forbids even the bare faithful corona embedding of its
concrete reduced group C-star algebra. -/
theorem not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF
    [Countable G] (h : ¬ IsGroupTheoreticMF G) :
    ¬ HasMFEmbedding (ReducedGroupCStarTrace.ReducedGroupCStar G) :=
  mt reducedGroupCStar_isGroupTheoreticMF_of_hasMFEmbedding h

/-! ## Simultaneous failure package -/

/-- Simultaneous failure of the equivalent MF formulations and the stronger
MF variants defined in this file.  The representation-theoretic PMatF,
PPermF, trace-PMF, PFF, and PPF conventions and the concrete maximal/reduced
C-star consequences are assembled separately in
`MFRepresentationVariants`.

This core package deliberately excludes soficity and hyperlinearity: neither
is definitionally one of these MF properties, and no converse implication is
asserted here.  It also excludes the unrelated modular-by-finite predicate
defined below. -/
structure FailsAllFormalizedMFVariants
    (G : Type u) [Group G] [Countable G] : Prop where
  not_isWeakMF : ¬ IsWeakMF G
  not_isOperatorMF : ¬ IsOperatorMF G
  not_isOperatorMFIncreasing : ¬ IsOperatorMFIncreasing G
  not_isGroupTheoreticMF : ¬ IsGroupTheoreticMF G
  not_isCDEOperatorMF : ¬ IsCDEOperatorMF G
  not_isUltraproductMF : ¬ IsUltraproductMF G
  not_isFiniteSetMF : ¬ IsFiniteSetMF G
  not_hasMFAlgebraUnitaryEmbedding : ¬ HasMFAlgebraUnitaryEmbedding G
  not_isTracePreservingMF : ¬ IsTracePreservingMF G
  not_isStrongMF : ¬ IsStrongMF G
  not_isTraceRegularMF : ¬ IsTraceRegularMF G
  not_isReducedGroupCStarMF : ¬ IsReducedGroupCStarMF G

/-- Failure of the group-theoretic MF property simultaneously rules out the
equivalent MF formulations and stronger variants defined above. -/
theorem failsAllFormalizedMFVariants_of_not_isGroupTheoreticMF
    [Countable G] (h : ¬ IsGroupTheoreticMF G) :
    FailsAllFormalizedMFVariants G := by
  have hOperator : ¬ IsOperatorMF G := by
    simpa [IsGroupTheoreticMF] using h
  exact {
    not_isWeakMF := fun hWeak ↦
      hOperator (IsWeakMF.isOperatorMF hWeak)
    not_isOperatorMF := hOperator
    not_isOperatorMFIncreasing := fun hIncreasing ↦
      hOperator ((isOperatorMFIncreasing_iff (G := G)).mp hIncreasing)
    not_isGroupTheoreticMF := h
    not_isCDEOperatorMF :=
      not_isCDEOperatorMF_of_not_isGroupTheoreticMF h
    not_isUltraproductMF :=
      not_isUltraproductMF_of_not_isGroupTheoreticMF h
    not_isFiniteSetMF :=
      not_isFiniteSetMF_of_not_isGroupTheoreticMF h
    not_hasMFAlgebraUnitaryEmbedding :=
      not_hasMFAlgebraUnitaryEmbedding_of_not_isGroupTheoreticMF h
    not_isTracePreservingMF :=
      not_isTracePreservingMF_of_not_isGroupTheoreticMF h
    not_isStrongMF := not_isStrongMF_of_not_isGroupTheoreticMF h
    not_isTraceRegularMF :=
      not_isTraceRegularMF_of_not_isGroupTheoreticMF h
    not_isReducedGroupCStarMF :=
      not_isReducedGroupCStarMF_of_not_isGroupTheoreticMF h }

/-! ## The unrelated modular-by-finite meaning -/

/-- A modular subgroup is a modular element of the subgroup lattice. -/
def IsModularSubgroup (H : Subgroup G) : Prop :=
  ∀ X Z : Subgroup G, X ≤ Z →
    X ⊔ (H ⊓ Z) = (X ⊔ H) ⊓ Z

/-- A subgroup is modular-by-finite when it contains a modular subgroup of
finite index. -/
def IsModularByFiniteSubgroup (X : Subgroup G) : Prop :=
  ∃ H : Subgroup G, H ≤ X ∧ IsModularSubgroup H ∧
    (H.comap X.subtype).FiniteIndex

/-- Modular-by-finite MF: every subgroup is modular-by-finite.  This has no
logical connection to matrix-factorization MF. -/
def IsModularByFiniteMF (G : Type u) [Group G] : Prop :=
  ∀ X : Subgroup G, IsModularByFiniteSubgroup X

end GroupApproximation
