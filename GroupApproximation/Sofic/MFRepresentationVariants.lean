import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Sofic.MFDefinitions

/-!
# Representation-theoretic MF conventions

Several current sources use `MF` for strong convergence to the left regular
representation, rather than for the equivalent faithful norm-corona
embedding of a countable group.  This file assigns separate names to the
representation-theoretic variants and proves the implication needed by the
non-MF obstruction.

* `IsPurelyMatricialField` is the trace-free PMatF convention: genuine
  finite-dimensional unitary representations converge to the reduced norm
  on every element of the algebraic group ring.
* `IsTracePMF` adds convergence of normalized characters to the regular
  character.
* `IsPFF` requires the image of every representation to be finite.
* `IsPurelyPermutationField` is Magee's trace-free PPermF convention.
* `IsPPF` is the trace-inclusive PPF convention: it records the same
  standard permutation data on top of PFF.  In both conventions the standard
  representation has dimension one less than the permutation degree and
  character `#Fix - 1`.

Thus both `IsPurelyPermutationField` and the chain
`IsPPF -> IsPFF -> IsTracePMF` imply `IsPurelyMatricialField`, hence
`IsOperatorMF`, for countable groups.  These are stronger variants, not new
names for soficity or hyperlinearity; neither of those properties occurs in
the failure package below.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## Genuine representations strongly converging in reduced norm -/

/-- A sequence of genuine finite-dimensional unitary representations whose
operator norms on the algebraic group ring converge to the corresponding
reduced group-C-star norms.  No trace convergence is included. -/
structure PurelyMatricialFieldApproximation (G : Type u) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  representation : ∀ n, G →* Matrix.unitaryGroup (model n) ℂ
  reducedNormConverges : ∀ c : G →₀ ℂ,
    Tendsto
      (fun n ↦ ‖matrixGroupRingEvaluation model
        (fun k g ↦ representation k g) n c‖)
      Filter.atTop
      (nhds ‖reducedGroupRingEvaluation (G := G) c‖)

/-- Purely matricial field in the trace-free Magee--de la Salle/Magee
sense: finite-dimensional representations strongly converge to the left
regular representation in reduced operator norm. -/
def IsPurelyMatricialField (G : Type u) [Group G] : Prop :=
  Nonempty (PurelyMatricialFieldApproximation G)

namespace PurelyMatricialFieldApproximation

/-- Forgetting exact multiplicativity gives the existing strong-MF
approximation. -/
noncomputable def toStrongMFApproximation
    (A : PurelyMatricialFieldApproximation G) : StrongMFApproximation G where
  model := A.model
  modelNonempty := A.modelNonempty
  map := fun n g ↦ A.representation n g
  asymptoticallyMultiplicative := by
    intro g h ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    have hmul :
        (A.representation n (g * h) :
            Matrix (A.model n) (A.model n) ℂ) =
          (A.representation n g : Matrix (A.model n) (A.model n) ℂ) *
            A.representation n h :=
      congrArg Subtype.val (map_mul (A.representation n) g h)
    rw [hmul, sub_self, norm_zero]
    exact hε.le
  reducedNormConverges := A.reducedNormConverges

end PurelyMatricialFieldApproximation

theorem IsPurelyMatricialField.isStrongMF
    (h : IsPurelyMatricialField G) : IsStrongMF G := by
  rcases h with ⟨A⟩
  exact ⟨A.toStrongMFApproximation⟩

/-- PMatF implies the faithful norm-corona formulation for countable
groups. -/
theorem IsPurelyMatricialField.isOperatorMF [Countable G]
    (h : IsPurelyMatricialField G) : IsOperatorMF G :=
  h.isStrongMF.isGroupTheoreticMF

/-! ## The trace-free purely permutation convention -/

/-- A trace-free PMatF approximation carried by standard irreducible
representations of finite permutation actions.

At stage `n`, the permutation action has degree `permutationDegree n`, the
matrix representation has dimension `permutationDegree n - 1`, and its
character is the standard character `#Fix(permutation n g) - 1`. -/
structure PurelyPermutationFieldApproximation (G : Type u) [Group G]
    extends PurelyMatricialFieldApproximation G where
  permutationDegree : ℕ → ℕ
  permutation : ∀ n, G →* Equiv.Perm (Fin (permutationDegree n))
  standardDimension : ∀ n,
    Fintype.card (model n) + 1 = permutationDegree n
  standardCharacter : ∀ n g,
    Matrix.trace
        (representation n g : Matrix (model n) (model n) ℂ) =
      ((((Function.fixedPoints (permutation n g)).ncard : ℤ) - 1 : ℤ) : ℂ)

/-- Purely permutation field in Magee's trace-free PPermF sense. -/
def IsPurelyPermutationField (G : Type u) [Group G] : Prop :=
  Nonempty (PurelyPermutationFieldApproximation G)

theorem IsPurelyPermutationField.isPurelyMatricialField
    (h : IsPurelyPermutationField G) : IsPurelyMatricialField G := by
  rcases h with ⟨A⟩
  exact ⟨A.toPurelyMatricialFieldApproximation⟩

theorem IsPurelyPermutationField.isOperatorMF [Countable G]
    (h : IsPurelyPermutationField G) : IsOperatorMF G :=
  h.isPurelyMatricialField.isOperatorMF

/-! ## Trace-PMF, PFF, and PPF -/

/-- A PMatF approximation whose normalized characters converge to the
regular character. -/
structure TracePMFApproximation (G : Type u) [Group G]
    extends PurelyMatricialFieldApproximation G where
  traceConverges : ∀ g : G,
    Tendsto
      (fun n ↦ normTrace (model n)
        (representation n g : Matrix (model n) (model n) ℂ))
      Filter.atTop
      (nhds (regularCharacter g))

/-- The trace-preserving PMF convention: genuine representations converge
both in reduced norm and in normalized character. -/
def IsTracePMF (G : Type u) [Group G] : Prop :=
  Nonempty (TracePMFApproximation G)

namespace TracePMFApproximation

/-- A trace-PMF model is, in particular, a trace-regular MF model: exact
multiplicativity may be forgotten, while the reduced-norm and normalized-trace
limits are retained verbatim. -/
noncomputable def toTraceRegularMFApproximation
    (A : TracePMFApproximation G) : TraceRegularMFApproximation G :=
  let S := A.toPurelyMatricialFieldApproximation.toStrongMFApproximation
  { separation := S.toWeakMFApproximation.separation
    separation_pos := S.toWeakMFApproximation.separation_pos
    model := A.model
    modelNonempty := A.modelNonempty
    map := fun n g ↦ A.representation n g
    asymptoticallyMultiplicative := S.asymptoticallyMultiplicative
    separatedEventually := S.toWeakMFApproximation.separatedEventually
    traceConverges := A.traceConverges
    reducedNormConverges := A.reducedNormConverges }

end TracePMFApproximation

/-- Trace-PMF implies the repository's trace-regular strong-MF predicate.
This is the formal bridge to the stronger notion called `MF` by GKMP; it is
strictly stronger than merely obtaining `IsOperatorMF`. -/
theorem IsTracePMF.isTraceRegularMF
    (h : IsTracePMF G) : IsTraceRegularMF G := by
  rcases h with ⟨A⟩
  exact ⟨A.toTraceRegularMFApproximation⟩

theorem IsTracePMF.isPurelyMatricialField
    (h : IsTracePMF G) : IsPurelyMatricialField G := by
  rcases h with ⟨A⟩
  exact ⟨A.toPurelyMatricialFieldApproximation⟩

theorem IsTracePMF.isOperatorMF [Countable G]
    (h : IsTracePMF G) : IsOperatorMF G :=
  h.isPurelyMatricialField.isOperatorMF

/-- A trace-PMF approximation whose representation has finite image at
every stage. -/
structure PFFApproximation (G : Type u) [Group G]
    extends TracePMFApproximation G where
  finiteImage : ∀ n,
    Set.Finite (Set.range fun g : G ↦ representation n g)

/-- Purely finite field: trace-PMF through genuine representations with
finite image at every stage. -/
def IsPFF (G : Type u) [Group G] : Prop :=
  Nonempty (PFFApproximation G)

theorem IsPFF.isTracePMF (h : IsPFF G) : IsTracePMF G := by
  rcases h with ⟨A⟩
  exact ⟨A.toTracePMFApproximation⟩

theorem IsPFF.isOperatorMF [Countable G]
    (h : IsPFF G) : IsOperatorMF G :=
  h.isTracePMF.isOperatorMF

/-- A PFF approximation carrying the standard irreducible representation
data of a finite permutation action.

At stage `n`, `permutation n` has degree `permutationDegree n`; the matrix
representation has dimension `permutationDegree n - 1`; and its character
is the standard character `#Fix(permutation n g) - 1`. -/
structure PPFApproximation (G : Type u) [Group G]
    extends PFFApproximation G where
  permutationDegree : ℕ → ℕ
  permutation : ∀ n, G →* Equiv.Perm (Fin (permutationDegree n))
  standardDimension : ∀ n,
    Fintype.card (model n) + 1 = permutationDegree n
  standardCharacter : ∀ n g,
    Matrix.trace
        (representation n g : Matrix (model n) (model n) ℂ) =
      ((((Function.fixedPoints (permutation n g)).ncard : ℤ) - 1 : ℤ) : ℂ)

/-- Purely permutation field: a PFF approximation by standard irreducible
representations of finite permutation groups. -/
def IsPPF (G : Type u) [Group G] : Prop :=
  Nonempty (PPFApproximation G)

theorem IsPPF.isPFF (h : IsPPF G) : IsPFF G := by
  rcases h with ⟨A⟩
  exact ⟨A.toPFFApproximation⟩

theorem IsPPF.isOperatorMF [Countable G]
    (h : IsPPF G) : IsOperatorMF G :=
  h.isPFF.isOperatorMF

/-! ## Uniform obstruction and the complete failure package -/

/-- Once a group is known not to be operator MF, every property implying
operator MF fails.  This is the reusable logical endpoint for additional
named conventions. -/
theorem not_of_implies_isOperatorMF
    (hG : ¬ IsOperatorMF G) (P : Prop)
    (hP : P → IsOperatorMF G) : ¬ P :=
  mt hP hG

/-- Simultaneous failure of every equivalent MF formulation, every stronger
representation-theoretic MF convention formalized above, and the bare and
separable MF predicates for the development's universe-relative maximal
group-C-star model and the concrete reduced group C-star algebra.

Soficity and hyperlinearity are deliberately absent: neither property is
known to imply operator MF. -/
structure FailsEveryStandardMFConvention
    (G : Type u) [Group G] [Countable G] : Prop
    extends FailsAllFormalizedMFVariants G where
  not_isPurelyMatricialField : ¬ IsPurelyMatricialField G
  not_isPurelyPermutationField : ¬ IsPurelyPermutationField G
  not_isTracePMF : ¬ IsTracePMF G
  not_isPFF : ¬ IsPFF G
  not_isPPF : ¬ IsPPF G
  not_maximalGroupCStar_hasMFEmbedding :
    ¬ HasMFEmbedding (MaximalGroupCStar G)
  not_maximalGroupCStar_isMFAlgebra :
    ¬ IsMFAlgebra (MaximalGroupCStar G)
  not_reducedGroupCStar_hasMFEmbedding :
    ¬ HasMFEmbedding (ReducedGroupCStarTrace.ReducedGroupCStar G)

/-- A single operator-MF obstruction supplies every field of
`FailsEveryStandardMFConvention`. -/
theorem failsEveryStandardMFConvention_of_not_isOperatorMF
    [Countable G] (h : ¬ IsOperatorMF G) :
    FailsEveryStandardMFConvention G := by
  have hBase : FailsAllFormalizedMFVariants G :=
    failsAllFormalizedMFVariants_of_not_isGroupTheoreticMF h
  have hReduced :
      ¬ HasMFEmbedding (ReducedGroupCStarTrace.ReducedGroupCStar G) :=
    not_hasMFEmbedding_reducedGroupCStar_of_not_isGroupTheoreticMF h
  have hMaximal : ¬ HasMFEmbedding (MaximalGroupCStar G) :=
    maximalGroupCStar_not_hasMFEmbedding_of_not_isOperatorMF G h
  exact {
    toFailsAllFormalizedMFVariants := hBase
    not_isPurelyMatricialField :=
      not_of_implies_isOperatorMF h _ IsPurelyMatricialField.isOperatorMF
    not_isPurelyPermutationField :=
      not_of_implies_isOperatorMF h _ IsPurelyPermutationField.isOperatorMF
    not_isTracePMF :=
      not_of_implies_isOperatorMF h _ IsTracePMF.isOperatorMF
    not_isPFF := not_of_implies_isOperatorMF h _ IsPFF.isOperatorMF
    not_isPPF := not_of_implies_isOperatorMF h _ IsPPF.isOperatorMF
    not_maximalGroupCStar_hasMFEmbedding := hMaximal
    not_maximalGroupCStar_isMFAlgebra := fun hMF ↦ hMaximal hMF.2
    not_reducedGroupCStar_hasMFEmbedding := hReduced }

end GroupApproximation
