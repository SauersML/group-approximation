import GroupApproximation.Analysis.GoldbringHartRoute
import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.UniversalCStarHNN
import GroupApproximation.Sofic.RegularCharacterGNS
import GroupApproximation.Sofic.WeakMFRegularTrace
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Metrizable.Basic

/-!
# Sentence-level closure for the HNN-corona-conjugator section

This file proves the unconditional infrastructure used at the beginning and
end of the manuscript section `HNN extensions with a corona conjugator`:

* the printed notion of a regular realization;
* faithfulness, and hence operator-MF, of every regularly realized group;
* the equivalence between arbitrary positive matrix dimensions and the
  strictly increasing convention used by `HasMFEmbedding`;
* a canonical tracial state on every norm-matrix corona;
* a faithful regular-trace corona representation associated to a
  `RegularTraceWeakMFApproximation`;
* regular realizability of every countable residually finite group;
* Britton injectivity of the base group;
* the universal C-star HNN mapping property and its faithful group lift; and
* the orthonormality and left-translation formulas in the regular-character
  GNS representation.

No MF permanence theorem for C-star amalgamated free products is assumed in
this file.  In particular, the manuscript's Shulman step remains a separate
formalization obligation.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace HNNCoronaConjugatorSentenceAudit

open Filter Matrix
open scoped Matrix.Norms.L2Operator Pointwise

noncomputable section

noncomputable local instance {X : Type*} : DecidableEq X := Classical.decEq X

universe u v

/-! ## The printed regular-realization definition -/

/-- The data called a *regular realization* in the manuscript. -/
structure RegularRealizationData (G : Type u) [Group G]
    (A : Type v) [CStarAlgebra A] where
  mf : IsMFAlgebra A
  rho : G →* unitary A
  tau : TracialState A
  regular : ∀ g : G, g ≠ 1 → tau (rho g : A) = 0

/-- A group is regularly realized when it has the printed data in a
same-small-universe C-star algebra.  This universe choice agrees with the
repository's other existential C-star predicates and is enough for all
countable presented groups used in the manuscript. -/
def IsRegularlyRealized (G : Type u) [Group G] : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI : CStarAlgebra A := inst
    Nonempty (RegularRealizationData G A)

namespace RegularRealizationData

variable {G : Type u} [Group G] {A : Type v} [CStarAlgebra A]

/-- Sentence `78762556875f`: the regular trace forces the group
representation in a regular realization to be injective. -/
theorem rho_injective (R : RegularRealizationData G A) :
    Function.Injective R.rho := by
  intro g h hgh
  have hmap : R.rho (g * h⁻¹) = 1 := by
    rw [map_mul, map_inv, hgh, mul_inv_cancel]
  by_contra hne
  have hprod : g * h⁻¹ ≠ 1 := fun hprod ↦ hne (mul_inv_eq_one.mp hprod)
  have hzero := R.regular (g * h⁻¹) hprod
  have hcoe : ((R.rho (g * h⁻¹) : unitary A) : A) = 1 :=
    congrArg Subtype.val hmap
  rw [hcoe, R.tau.apply_one] at hzero
  exact one_ne_zero hzero

/-- Sentence `78762556875f`: a regularly realized countable group is MF. -/
theorem isOperatorMF [Countable G] (R : RegularRealizationData G A) :
    IsOperatorMF G :=
  R.mf.2.isOperatorMF R.rho R.rho_injective

end RegularRealizationData

/-- The existential form of the preceding implication. -/
theorem isOperatorMF_of_isRegularlyRealized
    {G : Type u} [Group G] [Countable G]
    (hG : IsRegularlyRealized G) : IsOperatorMF G := by
  rcases hG with ⟨A, instA, ⟨R⟩⟩
  letI : CStarAlgebra A := instA
  exact R.isOperatorMF

/-! ## Arbitrary dimension sequences and the canonical corona trace -/

/-- Sentence `e04619ff6528`: a norm corona over any positive sequence of
finite models has the bare MF embedding property.  The proof is the literal
zero-corner padding construction in `MFAlgebraDimension.hasMFEmbedding_iff`.
-/
theorem normMatrixCorona_hasMFEmbedding_of_positive
    (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)) :
    letI : ∀ n, Nonempty (X n) := hne
    HasMFEmbedding (NormMatrixCStarCorona (fun n ↦ X n)) := by
  letI : ∀ n, Nonempty (X n) := hne
  apply (MFAlgebraDimension.hasMFEmbedding_iff
    (NormMatrixCStarCorona (fun n ↦ X n))).2
  refine ⟨X, hne, fun n ↦ Fintype.card_pos, NonUnitalStarAlgHom.id ℂ _, ?_⟩
  intro a b hab
  exact hab

/-- The ultrafilter used for the canonical tracial state below. -/
private def coronaUltrafilter : Ultrafilter ℕ :=
  Ultrafilter.of Filter.cofinite

private theorem coronaUltrafilter_le_cofinite :
    ((coronaUltrafilter : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
  Ultrafilter.of_le Filter.cofinite

/-- The normalized ultratrace, descended from bounded matrix sequences to
the cofinite norm-matrix corona. -/
def normMatrixCoronaTracialState
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    TracialState (NormMatrixCStarCorona (fun n ↦ X n)) :=
  (TracialUltraproduct.ultratraceFaithfulTracialState X
    coronaUltrafilter).toTracialState.compStarAlgHom
      (TracialUltraproduct.normMatrixCStarCoronaToTracialMatrixQuotient
        X coronaUltrafilter coronaUltrafilter_le_cofinite)

/-- Evaluation of the corona trace on a coordinatewise-unitary sequence. -/
theorem normMatrixCoronaTracialState_unitarySequence
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (a : ∀ n, Matrix.unitaryGroup (X n) ℂ) :
    normMatrixCoronaTracialState X
        ((unitarySequenceToCorona X a :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
      TracialUltraproduct.seqUltratrace X coronaUltrafilter
        (unitarySequenceBounded X a) := by
  change TracialUltraproduct.ultratrace X coronaUltrafilter
      (TracialUltraproduct.tracialMatrixQuotientMk X
        (coronaUltrafilter : Filter ℕ) (unitarySequenceBounded X a)) = _
  exact TracialUltraproduct.ultratrace_mk X coronaUltrafilter _

/-! ## From regular finite models to an exact regular corona representation -/

namespace RegularTraceWeakMFApproximation

variable {G : Type u} [Group G]

/-- The asymptotically multiplicative maps define an exact homomorphism into
the cofinite unitary-sequence corona. -/
def cofiniteUnitaryCoronaHom (M : RegularTraceWeakMFApproximation G) :
    G →* NormMatrixCoronaUnitary M.model := by
  have hnull : ∀ g h : G,
      (fun n ↦ M.map n g * M.map n h)⁻¹ *
          (fun n ↦ M.map n (g * h)) ∈
        nullCofiniteOpSubgroup M.model := by
    intro g h ε hε
    obtain ⟨N, hN⟩ :=
      M.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    rw [Nat.cofinite_eq_atTop]
    refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    change opLength (M.model n)
      ((M.map n g * M.map n h)⁻¹ * M.map n (g * h)) < ε
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  exact MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ M.map n g))
    (fun g h ↦ by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq.mpr (hnull g h)).symm)

/-- The same representation in the genuine norm-matrix C-star corona. -/
def cofiniteCStarCoronaHom (M : RegularTraceWeakMFApproximation G) :
    letI : ∀ n, Nonempty (M.model n) := fun n ↦
      Fintype.card_pos_iff.mp (M.modelNonempty n)
    G →* unitary (NormMatrixCStarCorona (fun n ↦ M.model n)) := by
  letI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  exact (normMatrixCoronaUnitaryEquiv M.model).toMonoidHom.comp
    (cofiniteUnitaryCoronaHom M)

@[simp]
theorem cofiniteCStarCoronaHom_apply
    (M : RegularTraceWeakMFApproximation G) (g : G) :
    letI : ∀ n, Nonempty (M.model n) := fun n ↦
      Fintype.card_pos_iff.mp (M.modelNonempty n)
    cofiniteCStarCoronaHom M g =
      unitarySequenceToCorona M.model (fun n ↦ M.map n g) := by
  letI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  change unitaryCoronaToCStarCoronaUnitary M.model
      (QuotientGroup.mk (fun n ↦ M.map n g)) = _
  exact unitaryCoronaToCStarCoronaUnitary_mk M.model _

/-- The exact corona representation remains faithful. -/
theorem cofiniteCStarCoronaHom_injective
    (M : RegularTraceWeakMFApproximation G) :
    letI : ∀ n, Nonempty (M.model n) := fun n ↦
      Fintype.card_pos_iff.mp (M.modelNonempty n)
    Function.Injective (cofiniteCStarCoronaHom M) := by
  letI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  intro g h hgh
  by_contra hne
  obtain ⟨N, hN⟩ := M.separatedEventually g h hne
  have hfar : ∀ᶠ n in Filter.cofinite,
      M.separation ≤
        ‖(M.map n g : Matrix (M.model n) (M.model n) ℂ) - M.map n h‖ := by
    rw [Nat.cofinite_eq_atTop]
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  have hseq : unitarySequenceToCorona M.model (fun n ↦ M.map n g) =
      unitarySequenceToCorona M.model (fun n ↦ M.map n h) := by
    simpa only [cofiniteCStarCoronaHom_apply] using hgh
  have hnull : IsNullCofiniteOpSeq M.model
      ((fun n ↦ M.map n h)⁻¹ * (fun n ↦ M.map n g)) := by
    apply (unitarySequenceToCorona_eq_one_iff M.model _).mp
    rw [map_mul, map_inv, hseq, inv_mul_cancel]
  have hclose : ∀ᶠ n in Filter.cofinite,
      ‖(M.map n g : Matrix (M.model n) (M.model n) ℂ) - M.map n h‖ <
        M.separation := by
    filter_upwards [hnull M.separation M.separation_pos] with n hn
    change opLength (M.model n) ((M.map n h)⁻¹ * M.map n g) <
      M.separation at hn
    rwa [opLength_inv_mul] at hn
  obtain ⟨n, hn₁, hn₂⟩ := (hfar.and hclose).exists
  exact (not_lt_of_ge hn₁) hn₂

/-- Sentences `4e967ddb2a22` and `3dfab3bc1ddb`: the exact corona
homomorphism induced by regular finite models has the regular character as
its corona trace. -/
theorem cofiniteCStarCoronaHom_regularTrace
    (M : RegularTraceWeakMFApproximation G) (g : G) (hg : g ≠ 1) :
    letI : ∀ n, Nonempty (M.model n) := fun n ↦
      Fintype.card_pos_iff.mp (M.modelNonempty n)
    normMatrixCoronaTracialState M.model
        (cofiniteCStarCoronaHom M g :
          NormMatrixCStarCorona (fun n ↦ M.model n)) = 0 := by
  letI : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  let pair : ∀ n, Matrix.unitaryGroup (M.model n) ℂ :=
    fun n ↦ M.map n g * (M.map n 1)⁻¹
  have hone : unitarySequenceToCorona M.model (fun n ↦ M.map n 1) = 1 := by
    rw [← cofiniteCStarCoronaHom_apply]
    exact map_one (cofiniteCStarCoronaHom M)
  have hpair : unitarySequenceToCorona M.model (fun n ↦ M.map n g) =
      unitarySequenceToCorona M.model pair := by
    change unitarySequenceToCorona M.model (fun n ↦ M.map n g) =
      unitarySequenceToCorona M.model
        ((fun n ↦ M.map n g) * (fun n ↦ M.map n 1)⁻¹)
    rw [map_mul, map_inv, hone, inv_one, mul_one]
  rw [cofiniteCStarCoronaHom_apply, hpair,
    normMatrixCoronaTracialState_unitarySequence]
  have hzeroAtTop : ∀ᶠ n in Filter.atTop,
      normTrace (M.model n) (unitarySequenceBounded M.model pair n) = 0 := by
    simpa [pair, Matrix.star_eq_conjTranspose] using
      M.regularTrace_eventually (g := g) (h := 1) hg
  have hzero : ∀ᶠ n in (coronaUltrafilter : Ultrafilter ℕ),
      normTrace (M.model n) (unitarySequenceBounded M.model pair n) = 0 := by
    apply hzeroAtTop.filter_mono
    simpa [Nat.cofinite_eq_atTop] using coronaUltrafilter_le_cofinite
  have hlimZero : Tendsto
      (fun n ↦ normTrace (M.model n)
        (unitarySequenceBounded M.model pair n))
      (coronaUltrafilter : Filter ℕ) (nhds 0) := by
    have heq :
        (fun n ↦ normTrace (M.model n)
          (unitarySequenceBounded M.model pair n)) =ᶠ[
            (coronaUltrafilter : Filter ℕ)] (fun _ ↦ 0) :=
      hzero
    exact tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique
    (TracialUltraproduct.tendsto_seqUltratrace
      M.model coronaUltrafilter (unitarySequenceBounded M.model pair))
    hlimZero

end RegularTraceWeakMFApproximation

/-! ## The separable C-star algebra generated by a group representation -/

section GeneratedCStar

variable {G : Type u} [Group G] {A : Type v} [CStarAlgebra A]

/-- The unital C-star subalgebra generated by the represented group. -/
def groupGeneratedCStar (rho : G →* unitary A) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (Set.range fun g : G ↦ (rho g : A))).topologicalClosure

instance groupGeneratedCStar_isClosed (rho : G →* unitary A) :
    IsClosed (groupGeneratedCStar rho : Set A) :=
  StarSubalgebra.isClosed_topologicalClosure _

noncomputable instance groupGeneratedCStar_cStarAlgebra
    (rho : G →* unitary A) : CStarAlgebra (groupGeneratedCStar rho) :=
  inferInstance

/-- The represented group, with codomain restricted to its generated
C-star subalgebra. -/
def groupGeneratedUnitaryHom (rho : G →* unitary A) :
    G →* unitary (groupGeneratedCStar rho) where
  toFun g := ⟨⟨(rho g : A),
    StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ ⟨g, rfl⟩)⟩, by
        constructor
        · apply Subtype.ext
          exact (rho g).property.1
        · apply Subtype.ext
          exact (rho g).property.2⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change (rho 1 : A) = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    apply Subtype.ext
    change (rho (g * h) : A) = (rho g : A) * (rho h : A)
    simp

@[simp]
theorem coe_groupGeneratedUnitaryHom (rho : G →* unitary A) (g : G) :
    (((groupGeneratedUnitaryHom rho g : unitary (groupGeneratedCStar rho)) :
      groupGeneratedCStar rho) : A) = (rho g : A) :=
  rfl

theorem groupGeneratedUnitaryHom_injective (rho : G →* unitary A)
    (hrho : Function.Injective rho) :
    Function.Injective (groupGeneratedUnitaryHom rho) := by
  intro g h hgh
  apply hrho
  apply Subtype.ext
  exact congrArg (fun z ↦ (((z : unitary (groupGeneratedCStar rho)) :
    groupGeneratedCStar rho) : A)) hgh

/-- A countable represented group generates a separable C-star algebra,
even when the ambient algebra is nonseparable. -/
theorem groupGeneratedCStar_separableSpace [Countable G]
    (rho : G →* unitary A) :
    TopologicalSpace.SeparableSpace (groupGeneratedCStar rho) := by
  let s : Set A := Set.range fun g : G ↦ (rho g : A)
  have hs : s.Countable := Set.countable_range _
  have hsStar : (star s : Set A).Countable := by
    rw [← Set.image_star]
    exact hs.image _
  let t : Set A := s ∪ star s
  have ht : t.Countable := by
    simpa [t] using hs.union hsStar
  letI : Countable ↑t := ht.to_subtype
  have hmonoid :
      ((Submonoid.closure t : Submonoid A) : Set A).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have hadjoin : TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
    rw [StarAlgebra.adjoin_eq_span]
    simpa [t] using hmonoid.isSeparable.span
  have hclosed : TopologicalSpace.IsSeparable
      ((groupGeneratedCStar rho : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      (((StarAlgebra.adjoin ℂ s).topologicalClosure :
        StarSubalgebra ℂ A) : Set A)
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadjoin.closure
  exact hclosed.separableSpace

/-- Restriction of a tracial state to the generated C-star subalgebra. -/
def groupGeneratedTrace (rho : G →* unitary A) (tau : TracialState A) :
    TracialState (groupGeneratedCStar rho) :=
  tau.compStarAlgHom (groupGeneratedCStar rho).subtype

/-- Passing from a possibly nonseparable MF ambient algebra to the C-star
algebra generated by a countable regular representation gives the literal
regular-realization data of the manuscript. -/
def generatedRegularRealization [Countable G]
    (hA : HasMFEmbedding A) (rho : G →* unitary A)
    (tau : TracialState A)
    (hregular : ∀ g : G, g ≠ 1 → tau (rho g : A) = 0) :
    RegularRealizationData G (groupGeneratedCStar rho) where
  mf := ⟨groupGeneratedCStar_separableSpace rho,
    hA.of_injective_nonUnitalStarAlgHom
      (groupGeneratedCStar rho).subtype.toNonUnitalStarAlgHom
      (fun x y hxy ↦ Subtype.ext hxy)⟩
  rho := groupGeneratedUnitaryHom rho
  tau := groupGeneratedTrace rho tau
  regular g hg := by
    simpa [groupGeneratedTrace] using hregular g hg

end GeneratedCStar

/-! ## Residually finite groups -/

/-- Sentence `53155bab3a91`: every countable residually finite group is
regularly realized.  The finite models are the exact regular-trace models
constructed in `WeakMFRegularTrace`; all passage to the norm corona and the
separable generated C-star algebra is performed above. -/
theorem residuallyFinite_isRegularlyRealized
    (G : Type) [Group G] [Countable G] [Group.ResiduallyFinite G] :
    IsRegularlyRealized G := by
  obtain ⟨M⟩ :=
    exists_regularTraceWeakMFApproximation_of_residuallyFinite (G := G)
  let hne : ∀ n, Nonempty (M.model n) := fun n ↦
    Fintype.card_pos_iff.mp (M.modelNonempty n)
  letI : ∀ n, Nonempty (M.model n) := hne
  let Q := NormMatrixCStarCorona (fun n ↦ M.model n)
  let rho : G →* unitary Q :=
    RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom M
  let tau : TracialState Q := normMatrixCoronaTracialState M.model
  let A := groupGeneratedCStar rho
  refine ⟨A, inferInstance, ⟨?_⟩⟩
  exact generatedRegularRealization
    (normMatrixCorona_hasMFEmbedding_of_positive M.model hne)
    rho tau
    (fun g hg ↦
      RegularTraceWeakMFApproximation.cofiniteCStarCoronaHom_regularTrace M g hg)

/-! ## Britton injectivity and the universal C-star HNN object -/

/-- Sentence `1127a37962dc`: the canonical base map into an HNN extension
is injective. -/
theorem hnnExtension_base_injective
    {G : Type u} [Group G] {S T : Subgroup G} (theta : S ≃* T) :
    Function.Injective
      (HNNExtension.of : G →* HNNExtension G S T theta) :=
  HNNExtension.of_injective theta

/-- Sentence `15484f411370`: the concrete universal C-star HNN algebra has
the stated universal mapping property. -/
theorem universalCStarHNN_mappingProperty
    {D : Type u} [CStarAlgebra D]
    (B0 B1 : StarSubalgebra ℂ D) (theta : B0 ≃⋆ₐ[ℂ] B1)
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    {E : Type u} [CStarAlgebra E] [Nontrivial E]
    (pi : D →⋆ₐ[ℂ] E) (v : unitary E)
    (hcov : ∀ b : B0,
      (v : E) * pi (b : D) = pi ((theta b : B1) : D) * (v : E)) :
    ∃! f : UniversalCStarHNN B0 B1 theta →⋆ₐ[ℂ] E,
      (∀ d : D, f (universalCStarHNNBase B0 B1 theta d) = pi d) ∧
      f (universalCStarHNNStable B0 B1 theta :
        UniversalCStarHNN B0 B1 theta) = (v : E) :=
  universalCStarHNN_existsUnique_lift B0 B1 theta pi v hcov

/-- Sentences `1a354a191c9a` and `62f684dc2b6c`, in their exact abstract
form: a covariant representation induces a group-HNN representation in the
universal C-star HNN algebra, and a faithful evaluation coordinate makes it
injective. -/
theorem universalCStarHNN_groupLift_injective
    {D : Type u} [CStarAlgebra D]
    (B0 B1 : StarSubalgebra ℂ D) (theta : B0 ≃⋆ₐ[ℂ] B1)
    [Nonempty (CStarHNNRepresentation B0 B1 theta)]
    {G : Type v} [Group G] {S T : Subgroup G} (phi : S ≃* T)
    (R : CStarHNNRepresentation B0 B1 theta)
    (rho : G →* unitary (UniversalCStarHNN B0 B1 theta))
    (hrel : ∀ s : S,
      universalCStarHNNStable B0 B1 theta * rho (s : G) =
        rho ((phi s : T) : G) * universalCStarHNNStable B0 B1 theta)
    (hfaithful : Function.Injective
      (universalCStarHNNGroupLiftEval B0 B1 theta phi R rho hrel)) :
    Function.Injective
      (universalCStarHNNGroupLift B0 B1 theta phi rho hrel) :=
  universalCStarHNNGroupLift_injective_of_eval
    B0 B1 theta phi R rho hrel hfaithful

/-! ## The regular-character GNS formulas -/

/-- Sentence `601ed9f89a31`: the regular-character GNS orbit vectors are
orthonormal. -/
theorem regularCharacterGNS_orbit_orthonormal
    {G : Type u} [Group G] (g h : G) :
    inner ℝ
        (KazhdanGNS.kernelVector
          (RegularCharacterGNS.positiveDefiniteFunction (G := G)) g)
        (KazhdanGNS.kernelVector
          (RegularCharacterGNS.positiveDefiniteFunction (G := G)) h) =
      if g = h then 1 else 0 := by
  classical
  exact RegularCharacterGNS.inner_kernelVector g h

/-- Sentence `909e382a20f9`: the GNS representation acts on those vectors
by left translation. -/
theorem regularCharacterGNS_left_translation
    {G : Type u} [Group G] (s g : G) :
    KazhdanGNS.representation
        (RegularCharacterGNS.positiveDefiniteFunction (G := G)) s
        (KazhdanGNS.kernelVector
          (RegularCharacterGNS.positiveDefiniteFunction (G := G)) g) =
      KazhdanGNS.kernelVector
        (RegularCharacterGNS.positiveDefiniteFunction (G := G)) (s * g) :=
  KazhdanGNS.representation_kernelVector _ _ _

end

end HNNCoronaConjugatorSentenceAudit
end OneSidedMFRadical
end Manuscript
end GroupApproximation
