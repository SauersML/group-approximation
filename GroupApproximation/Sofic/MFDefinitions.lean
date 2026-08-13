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
between the group-corona, matrix-ultraproduct, finite-set, and MF-algebra
formulations, and records the valid one-way implications from the stronger
trace, regular, reduced-C-star, and full-C-star formulations.

`IsModularByFiniteMF` is deliberately kept separate: its letters stand for
“modular-by-finite” and it is an unrelated subgroup-lattice property.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## Four equivalent group approximation formulations -/

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

theorem isMFAlgebraEmbedding_iff_isGroupTheoreticMF [Countable G] :
    IsMFAlgebraEmbedding G ↔ IsGroupTheoreticMF G :=
  isMFAlgebraEmbedding_iff_isOperatorMF G

/-- The four standard group meanings of MF, together with the literal CDE
corona formulation, hold simultaneously exactly when any one of them holds. -/
theorem standardMFDefinitions_iff [Countable G] :
    IsGroupTheoreticMF G ↔
      IsCDEOperatorMF G ∧ IsUltraproductMF G ∧ IsFiniteSetMF G ∧
        IsMFAlgebraEmbedding G := by
  constructor
  · intro h
    exact ⟨(isCDEOperatorMF_iff_isOperatorMF G).mpr h,
      h.isUltraproductMF,
      isFiniteSetMF_iff_isGroupTheoreticMF.mpr h,
      isMFAlgebraEmbedding_iff_isGroupTheoreticMF.mpr h⟩
  · rintro ⟨_hcde, _hultra, hfinite, _halgebra⟩
    exact isFiniteSetMF_iff_isGroupTheoreticMF.mp hfinite

/-! ## Trace-preserving and regular MF -/

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

/-- A regular MF approximation is trace-preserving and, in addition,
recovers the reduced operator norm of every algebraic group-ring element. -/
structure RegularMFApproximation (G : Type u) [Group G]
    extends TracePreservingMFApproximation G where
  reducedNormConverges : ∀ c : G →₀ ℂ,
    Tendsto
      (fun n ↦ ‖matrixGroupRingEvaluation model map n c‖)
      Filter.atTop
      (nhds ‖reducedGroupRingEvaluation (G := G) c‖)

/-- Regular MF in the strong, reduced-norm-preserving sense. -/
def IsRegularMF (G : Type u) [Group G] : Prop :=
  Nonempty (RegularMFApproximation G)

theorem IsRegularMF.isTracePreservingMF
    (h : IsRegularMF G) : IsTracePreservingMF G := by
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

theorem IsRegularMF.isGroupTheoreticMF [Countable G]
    (h : IsRegularMF G) : IsGroupTheoreticMF G :=
  h.isTracePreservingMF.isGroupTheoreticMF

/-! ## Reduced and full group C-star algebra formulations -/

/-- The concrete closed regular-representation algebra, bundled as a complex
C-star algebra. -/
noncomputable instance reducedGroupCStarCStarAlgebra :
    CStarAlgebra (ReducedGroupCStarTrace.ReducedGroupCStar G) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace :=
    (StarSubalgebra.isClosed_topologicalClosure
      (StarAlgebra.adjoin ℂ
        (Set.range (ReducedGroupCStarTrace.leftRegularOperator G)))).completeSpace_coe
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Reduced-C-star MF: the concrete reduced group C-star algebra is an MF
C-star algebra. -/
def IsReducedGroupCStarMF (G : Type u) [Group G] : Prop :=
  IsMFAlgebra (ReducedGroupCStarTrace.ReducedGroupCStar G)

theorem IsReducedGroupCStarMF.isGroupTheoreticMF [Countable G]
    (h : IsReducedGroupCStarMF G) : IsGroupTheoreticMF G := by
  rcases h with ⟨X, hne, hX, hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  let ue : unitary (ReducedGroupCStarTrace.ReducedGroupCStar G) →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (Unitary.map (starAlgHomToStarMonoidHom e)).toMonoidHom
  have hcde : IsCDEOperatorMF G :=
    ⟨X, hne, hX, hmono, ue.comp (reducedLeftRegularUnitaryHom G),
      (Unitary.map_injective he).comp
        (reducedLeftRegularUnitaryHom_injective G)⟩
  exact (isCDEOperatorMF_iff_isOperatorMF G).mp hcde

/-- A realization of the full group C-star algebra, expressed by its
universal property for unitary representations. -/
structure FullGroupCStarAlgebra (G : Type u) [Group G] where
  carrier : Type u
  inst : CStarAlgebra carrier
  inclusion : letI : CStarAlgebra carrier := inst
    G →* unitary carrier
  inclusionInjective : Function.Injective inclusion
  universal : ∀ (B : Type u) (instB : CStarAlgebra B),
    letI : CStarAlgebra B := instB
    letI : CStarAlgebra carrier := inst
    ∀ rho : G →* unitary B,
      ∃! f : carrier →⋆ₐ[ℂ] B,
        ∀ g : G, f (inclusion g : carrier) = (rho g : B)

/-- Full-C-star MF: a full group C-star realization is an MF algebra. -/
def IsFullGroupCStarMF (G : Type u) [Group G] : Prop :=
  ∃ C : FullGroupCStarAlgebra G,
    letI : CStarAlgebra C.carrier := C.inst
    IsMFAlgebra C.carrier

theorem IsFullGroupCStarMF.isGroupTheoreticMF [Countable G]
    (h : IsFullGroupCStarMF G) : IsGroupTheoreticMF G := by
  rcases h with ⟨C, hC⟩
  letI : CStarAlgebra C.carrier := C.inst
  rcases hC with ⟨X, hne, hX, hmono, e, he⟩
  letI : ∀ n, Nonempty (X n) := hne
  let ue : unitary C.carrier →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (Unitary.map (starAlgHomToStarMonoidHom e)).toMonoidHom
  have hcde : IsCDEOperatorMF G :=
    ⟨X, hne, hX, hmono, ue.comp C.inclusion,
      (Unitary.map_injective he).comp C.inclusionInjective⟩
  exact (isCDEOperatorMF_iff_isOperatorMF G).mp hcde

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

theorem not_isMFAlgebraEmbedding_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsMFAlgebraEmbedding G :=
  mt isMFAlgebraEmbedding_iff_isGroupTheoreticMF.mp h

theorem not_isTracePreservingMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsTracePreservingMF G :=
  mt IsTracePreservingMF.isGroupTheoreticMF h

theorem not_isRegularMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsRegularMF G :=
  mt IsRegularMF.isGroupTheoreticMF h

theorem not_isReducedGroupCStarMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsReducedGroupCStarMF G :=
  mt IsReducedGroupCStarMF.isGroupTheoreticMF h

theorem not_isFullGroupCStarMF_of_not_isGroupTheoreticMF [Countable G]
    (h : ¬ IsGroupTheoreticMF G) : ¬ IsFullGroupCStarMF G :=
  mt IsFullGroupCStarMF.isGroupTheoreticMF h

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
