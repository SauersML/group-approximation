import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Criterion.FiniteQuotientBlindness
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Monsters.CliffordAlgebraLamp
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.DefectSaturation
import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.NormalKazhdanHyperlinearKilled
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Sofic.OperatorMFLocalNormalization

/-!
# Exact outer-form declarations for the non-MF manuscript

Each declaration in this file packages the complete proposition displayed by
one numbered manuscript claim.  Reusable mathematical proofs remain in their
natural modules; this file is the machine-checked specification boundary.
-/

namespace GroupApproximation
namespace ManuscriptExactWrappers

open scoped Pointwise commutatorElement
open ReducedGroupCStarTrace

noncomputable section

universe u v w

/-! ## Definition-level equivalences -/

/-- The three equivalences stated with the manuscript's definition of an MF
group: genuine C-star corona versus unitary sequences, normalized local
models, and arbitrary versus strictly increasing positive dimensions. -/
theorem manuscriptMFDefinitionEquivalences :
    ∀ (G : Type u) [Group G] [Countable G],
    (IsCDEOperatorMF G ↔ IsOperatorMF G) ∧
      (IsOperatorMF G ↔ IsNormApproximable G 1) ∧
      (IsOperatorMFIncreasing G ↔ IsOperatorMF G) := by
  intro G _ _
  exact ⟨isCDEOperatorMF_iff_isOperatorMF G,
    OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one,
    isOperatorMFIncreasing_iff⟩

/-! ## Finite-dimensional obstruction -/

/-- Both clauses of manuscript Theorem B: the marked commutator and the
entire intrinsic compression-centralizer defect are killed by every
finite-dimensional representation, over every field. -/
theorem manuscriptTheoremB :
    (∀ (k : Type u) (V : Type v) (H : Type w)
      [Field k] [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [Group H]
      (π : H →* (Module.End k V)ˣ) (Γ : Subgroup H) (t c a : H),
      a ∈ Γ →
      (∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) →
      (∀ γ ∈ Γ, c * γ = γ * c) →
      π ⁅t * c * t⁻¹, a * (t * c * t⁻¹) * a⁻¹⁆ = 1) ∧
      (∀ (k : Type u) (V : Type v) (H : Type)
        [Field k] [AddCommGroup V] [Module k V]
        [FiniteDimensional k V] [Group H]
        (π : H →* (Module.End k V)ˣ) (Γ : Subgroup H),
        compressionCentralizerDefect Γ ≤ π.ker) := by
  constructor
  · intro k V H _ _ _ _ _ π Γ t c a ha hcomp hcen
    exact map_marked_commutator_eq_one_units π ha hcomp hcen
  · intro k V H _ _ _ _ _ π Γ
    have hlinear : compressionCentralizerDefect Γ ≤
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp π).ker :=
      compressionCentralizerDefect_le_ker
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp π) Γ
    intro g hg
    have hmap := MonoidHom.mem_ker.mp (hlinear hg)
    apply MonoidHom.mem_ker.mpr
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).injective
      (by simpa using hmap)

/-! ## Clifford and affine witness packages -/

/-- The concrete Clifford-lamp construction used by the manuscript: its
distinguished sign is a nontrivial central involution, site generators are
involutions with the Clifford commutator law, and permutations relabel the
sites while fixing the sign. -/
theorem manuscriptCliffordConstruction :
    ∀ X : Type u,
    (CliffordAlgebraLamp.euclidQ X =
        LinearMap.BilinMap.toQuadraticMap
          (CliffordAlgebraLamp.dotForm X) ∧
      (∀ x : X,
        (CliffordAlgebraLamp.lampUnit X x :
          CliffordAlgebra (CliffordAlgebraLamp.euclidQ X)) =
            CliffordAlgebra.ι (CliffordAlgebraLamp.euclidQ X)
              (Finsupp.single x 1)) ∧
      CliffordAlgebraLamp.lampGroup X =
        Subgroup.closure
          (Set.range (CliffordAlgebraLamp.lampUnit X) ∪
            {CliffordAlgebraLamp.zUnit X}) ∧
      (∀ x : X,
        ((CliffordAlgebraLamp.lampGen X x :
            CliffordAlgebraLamp.lampGroup X) :
          (CliffordAlgebra (CliffordAlgebraLamp.euclidQ X))ˣ) =
            CliffordAlgebraLamp.lampUnit X x) ∧
      (((CliffordAlgebraLamp.zGen X :
          CliffordAlgebraLamp.lampGroup X) :
        (CliffordAlgebra (CliffordAlgebraLamp.euclidQ X))ˣ) =
          CliffordAlgebraLamp.zUnit X) ∧
      ((CliffordAlgebraLamp.zUnit X :
        CliffordAlgebra (CliffordAlgebraLamp.euclidQ X)) = -1) ∧
      CliffordAlgebraLamp.zGen X ^ 2 = 1 ∧
      CliffordAlgebraLamp.zGen X ≠ 1 ∧
      CliffordAlgebraLamp.zGen X ∈
        Subgroup.center ↥(CliffordAlgebraLamp.lampGroup X) ∧
      (∀ x : X, CliffordAlgebraLamp.lampGen X x ^ 2 = 1) ∧
      (∀ x y : X, x ≠ y →
        CliffordAlgebraLamp.lampGen X x *
            CliffordAlgebraLamp.lampGen X y =
          CliffordAlgebraLamp.zGen X *
            (CliffordAlgebraLamp.lampGen X y *
              CliffordAlgebraLamp.lampGen X x))) ∧
      ((∀ (σ : Equiv.Perm X) (x : X),
        CliffordAlgebraLamp.permHom X σ
            (CliffordAlgebraLamp.lampGen X x) =
          CliffordAlgebraLamp.lampGen X (σ x)) ∧
      (∀ σ : Equiv.Perm X,
        CliffordAlgebraLamp.permHom X σ
            (CliffordAlgebraLamp.zGen X) =
          CliffordAlgebraLamp.zGen X)) := by
  intro X
  refine ⟨?_, CliffordAlgebraLamp.cliffordLamp_permutation_package X⟩
  refine ⟨rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl, rfl,
    CliffordAlgebraLamp.zGen_sq X,
    CliffordAlgebraLamp.zGen_ne_one X,
    CliffordAlgebraLamp.zGen_mem_center X,
    CliffordAlgebraLamp.lampGen_sq X, ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  change CliffordAlgebraLamp.lamp X x * CliffordAlgebraLamp.lamp X y =
    (-1) * (CliffordAlgebraLamp.lamp X y * CliffordAlgebraLamp.lamp X x)
  rw [CliffordAlgebraLamp.lamp_mul_lamp_of_ne X hxy, neg_one_mul]

open LiteralNonMFPresentation LiteralNonMFLinearWitness ExplicitLinearModel

/-- Every clause of the manuscript's explicit affine linear model. -/
theorem manuscriptLinearModel :
    ((xU : Mat) = !![0,1,0,0; 0,0,1,0; 1,0,0,0; 0,0,0,1]) ∧
      ((yU : Mat) = !![1,0,1,0; 0,-1,-1,0; 0,1,0,0; 0,0,0,1]) ∧
      ((zU : Mat) = !![0,1,0,0; 1,0,0,0; -1,-1,-1,0; 0,0,0,1]) ∧
      ((v1U : Mat) = !![1,0,0,1; 0,1,0,0; 0,0,1,0; 0,0,0,1]) ∧
      ((v2U : Mat) = !![1,0,0,0; 0,1,0,1; 0,0,1,0; 0,0,0,1]) ∧
      ((v3U : Mat) = !![1,0,0,0; 0,1,0,0; 0,0,1,1; 0,0,0,1]) ∧
      ((dU : Mat) = !![2,0,0,0; 0,2,0,0; 0,0,2,0; 0,0,0,1]) ∧
      gammaBar = Subgroup.closure {xU, yU, zU, v1U, v2U, v3U} ∧
      dU = ⟨dM, dInvM, dM_inv, dM_inv'⟩ ∧
      (∀ u : gammaBar,
        ((conjD u : gammaBar) : Matˣ) = dU * (u : Matˣ) * dU⁻¹) ∧
      (∀ r ∈ baseRelators,
      FreeGroup.lift matrixBaseGenerator r = 1) ∧
      Function.Injective conjD ∧
      conjD v1G = v1G ^ 2 ∧
      conjD v2G = v2G ^ 2 ∧
      conjD v3G = v3G ^ 2 ∧
      conjD xG = xG ∧ conjD yG = yG ∧ conjD zG = zG ∧
      v1G ∉ Set.range conjD := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, fun _ ↦ rfl,
    matrixBaseGenerator_kills, conjD_injective,
    conjD_v1G, conjD_v2G, conjD_v3G,
    conjD_xG, conjD_yG, conjD_zG, v1G_not_mem_range⟩

/-! ## Corona and marked-pattern packages -/

/-- Exact natural-dimension form of the manuscript's unitary lifting lemma. -/
theorem manuscriptUnitaryLifting :
    ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa using hd n)
    ∀ x : unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      ∃ u : ∀ n, Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ,
        unitarySequenceToCorona (fun n ↦ naturalFiniteModel (d n)) u = x := by
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  dsimp only
  intro x
  obtain ⟨q, hq⟩ := unitaryCoronaToCStarCoronaUnitary_surjective
    (fun n ↦ naturalFiniteModel (d n)) x
  induction q using Quotient.inductionOn with
  | _ u => exact ⟨u, by simpa using hq⟩

/-- The canonical unitary-sequence/C-star-corona isomorphism, including its
formula on every represented sequence. -/
theorem manuscriptUnitaryCoronaEquivalence :
    ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa using hd n)
    ∃ kappa : NormMatrixCoronaUnitary
        (fun n ↦ naturalFiniteModel (d n)) ≃*
        unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
      kappa.toMonoidHom = unitaryCoronaToCStarCoronaUnitary
        (fun n ↦ naturalFiniteModel (d n)) ∧
        ∀ u : ∀ n, Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ,
          kappa (QuotientGroup.mk u) = unitarySequenceToCorona
            (fun n ↦ naturalFiniteModel (d n)) u := by
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  dsimp only
  exact ⟨normMatrixCoronaUnitaryEquiv
      (fun n ↦ naturalFiniteModel (d n)), rfl,
    unitaryCoronaToCStarCoronaUnitary_mk
      (fun n ↦ naturalFiniteModel (d n))⟩

/-- Exact data and defect subgroup of a marked Kazhdan pattern. -/
theorem manuscriptMarkedKazhdanPattern :
    ∀ {Gamma : Type} {H : Type u} [Group Gamma] [Group H]
      [_countableGamma : Countable Gamma] [_countableH : Countable H]
      (C : KazhdanCompressionCore Gamma H),
    HasKazhdanPropertyT.{0, 0} Gamma ∧
      HasKazhdanPropertyTComplex.{0, w} Gamma ∧
      (∀ gamma : Gamma, ∃ delta : Gamma,
        C.t * C.iota gamma * C.t⁻¹ = C.iota delta) ∧
      (∀ gamma : Gamma, Commute C.c (C.iota gamma)) ∧
      C.defectNormal = Subgroup.normalClosure
        (Set.range fun gamma : Gamma ↦
          ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) ∧
      C.defectNormal.Normal := by
  intro Gamma H _ _ _ _ C
  exact ⟨C.kazhdan, hasKazhdanPropertyT_iff_textbook.mp C.kazhdan,
    C.compresses, C.comm_c, rfl, inferInstance⟩

/-- Exact natural-dimension form of the finite-normal obstruction criterion:
every homomorphism into the unitary group of the genuine norm-matrix C-star
corona maps the specified finite normal subgroup to the identity. -/
theorem manuscriptFiniteNormalObstructionCriterion :
    ∀ {Gamma H : Type} [Group Gamma] [Group H]
      [_countableGamma : Countable Gamma] [Countable H]
      (C : KazhdanCompressionCore Gamma H)
      (F : Subgroup H) [Finite F] [F.Normal]
      (hF : F ≤ C.defectNormal)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ Theta.ker := by
  intro Gamma H _ _ _ _ C F _ _ hF d hd
  exact C.finiteNormal_le_normMatrixCStarCoronaKernel F hF
    (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by
      simpa using hd n)

/-- Exact natural-dimension form of the normal-Kazhdan obstruction: every
homomorphism into the unitary group of the genuine norm-matrix C-star
corona maps a normal property-`(T)` subgroup of the compression defect to
the identity.  No finiteness, centrality, or torsion hypothesis appears. -/
theorem manuscriptNormalKazhdanObstruction :
    ∀ {Gamma H : Type} [Group Gamma] [Group H]
      [_countableGamma : Countable Gamma] [Countable H]
      (C : KazhdanCompressionCore Gamma H)
      (K : Subgroup H) [K.Normal]
      (hT : HasKazhdanPropertyT.{0, 0} K)
      (hK : K ≤ C.defectNormal)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      K ≤ Theta.ker := by
  intro Gamma H _ _ _ _ C K _ hT hK d hd
  exact C.normalKazhdan_le_normMatrixCStarCoronaKernel K hT hK
    (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by
      simpa using hd n)

/-- Exact coordinate finite-normal-corner conclusion for literal positive
natural matrix dimensions. -/
theorem manuscriptCoordinateFiniteNormalCorner :
    ∀ {H : Type} [Group H] [Countable H]
      (F : Subgroup H) [Finite F] [F.Normal]
      {I : Type} (U : Ultrafilter I) (d : I → ℕ)
      (_hd : ∀ i, 0 < d i)
      (rho : H →* UniversalWeakMF U (fun i ↦ naturalFiniteModel (d i)))
      (_hnontrivial : ∃ f : F, rho f ≠ 1),
    ∃ B : OpAlmostRepresentation H,
      (∀ n, 0 < Fintype.card (B.model n)) ∧
      letI : Fintype F := Fintype.ofFinite F
      KazhdanCornerMatrices.OpNormVanishing B (fun n ↦
        ∑ f : F, (B.map n (f : H) :
          Matrix (B.model n) (B.model n) ℂ)) := by
  intro H _ _ F _ _ I U d _hd rho _hnontrivial
  letI : ∀ i, Nonempty (naturalFiniteModel (d i)) := fun i ↦
    Fintype.card_pos_iff.mp (by
      simpa using _hd i)
  obtain ⟨B, hsum⟩ :=
    FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing
      F U (fun i ↦ naturalFiniteModel (d i)) rho _hnontrivial
  exact ⟨B, B.modelNonempty, hsum⟩

/-- Exact outer-form version of the manuscript's compression-defect collapse:
the squared normalized Hilbert--Schmidt distance tends to zero, which is
equivalent to convergence of the normalized Hilbert--Schmidt norm itself. -/
theorem manuscriptCompressionDefectsCollapse :
    ∀ {Gamma H : Type} [Group Gamma] [Group H]
      (C : KazhdanCompressionCore Gamma H)
      (B : OpAlmostRepresentation H),
    ∀ gamma : Gamma, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N, ∀ n ≥ N,
        hsDistSq (B.model n)
          (B.map n
            ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆)
          (B.map n 1) ≤ epsilon := by
  intro Gamma H _ _ C B
  exact C.compressionDefects_hsTrivial B

/-! ## MF radical and quotient -/

/-- The MF radical is literally the intersection-of-kernels predicate and is
a normal subgroup. -/
theorem manuscriptMFRadical :
    ∀ (G : Type u) [Group G] [_countableG : Countable G],
    ((∀ x : G, x ∈ manuscriptCoronaMFResidual G ↔
      ∀ (d : ℕ → ℕ), ∀ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : G →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          rho x = 1)) ∧
      (manuscriptCoronaMFResidual G).Normal := by
  intro G _ _
  exact ⟨fun _ ↦ Iff.rfl, inferInstance⟩

/-- Functoriality of the MF radical together with the literal marked-word
consequence printed in the portability lemma. -/
theorem manuscriptRadicalPortability :
    ∀ (G1 : Type u) [Group G1] [_countableG1 : Countable G1]
      (G2 : Type v) [Group G2] [Countable G2],
    (∀ f : G1 →* G2,
      (manuscriptCoronaMFResidual G1).map f ≤ manuscriptCoronaMFResidual G2) ∧
      (∀ (phi : MarkedGroup →* G2),
        phi mark ≠ 1 →
          ¬ IsCDEOperatorMF G2) := by
  intro G1 _ _ G2 _ _
  constructor
  · exact map_manuscriptCoronaMFResidual_le
  · intro phi hsurvive hMF
    have himage : phi mark ∈ manuscriptCoronaMFResidual G2 :=
      map_manuscriptCoronaMFResidual_le phi
        ⟨mark,
          LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual,
          rfl⟩
    have hbot : manuscriptCoronaMFResidual G2 = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
    rw [hbot] at himage
    exact hsurvive (Subgroup.mem_bot.mp himage)

/-- All clauses of the universal-MF-quotient proposition, using the literal
CDE definition at the public boundary.  The faithful corona representation
is constructed on the quotient first and then composed with the quotient
map, so no coordinatewise radical-killing diagonal condition is omitted. -/
theorem manuscriptUniversalMFQuotient :
    ∀ (G : Type u) [Group G] [Countable G],
    letI : Countable (G ⧸ manuscriptCoronaMFResidual G) :=
      Function.Surjective.countable
        (QuotientGroup.mk'_surjective (manuscriptCoronaMFResidual G))
    (∃ (d : ℕ → ℕ), ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∃ rho : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho.ker = manuscriptCoronaMFResidual G) ∧
      IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G) ∧
      (∀ {H : Type v} [Group H] [Countable H]
        (f : G →* H), IsCDEOperatorMF H →
          ∃ fBar : (G ⧸ manuscriptCoronaMFResidual G) →* H,
            fBar.comp (QuotientGroup.mk' (manuscriptCoronaMFResidual G)) = f) ∧
      (IsCDEOperatorMF G ↔ manuscriptCoronaMFResidual G = ⊥) := by
  intro G _ _
  refine
    ⟨exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual,
      manuscriptCoronaMFQuotient_isCDEOperatorMF, ?_, ?_⟩
  · intro H _ _ f hH
    exact
      (existsUnique_manuscriptCoronaMFQuotient_factorization_to_isCDEOperatorMF
        f hH).exists
  · exact isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot

/-- Exact factorization and equality criterion for a proposed radical. -/
theorem manuscriptExactRadicalFromCandidateQuotient :
    ∀ (G : Type u) [Group G] [Countable G]
      (N : Subgroup G) [N.Normal] (hN : N ≤ manuscriptCoronaMFResidual G),
    letI : Countable (G ⧸ N) :=
      Function.Surjective.countable (QuotientGroup.mk'_surjective N)
    (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∀ rho : G →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      ∃! rhoBar : (G ⧸ N) →*
          unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
        rhoBar.comp (QuotientGroup.mk' N) = rho) ∧
      (IsCDEOperatorMF (G ⧸ N) → manuscriptCoronaMFResidual G = N) := by
  intro G _ _ N _ hN
  constructor
  · intro d hd rho
    exact existsUnique_quotient_factorization_to_manuscriptCorona
      N hN d hd rho
  · intro hquot
    exact manuscriptCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
      N hN hquot

/-! ## Faithful trace and stable finiteness -/

/-- Every clause of the manuscript's faithful-trace lemma, including the
explicit natural-matrix specialization of stable finiteness. -/
theorem manuscriptFaithfulTraceAndStableFiniteness :
    (∀ (G : Type u) [Group G] [_countableG : Countable G],
      let tau := canonicalFaithfulTracialState G
      ∀ T : ReducedGroupCStar G,
        tau (star T * T) = 0 ↔ T = 0) ∧
      (∀ (A : Type u) [CStarAlgebra A],
        FaithfulTracialState A →
        ∀ (I : Type*) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I A,
          star v * v = 1 → v * star v = 1) ∧
      (∀ (A : Type u) [CStarAlgebra A],
        FaithfulTracialState A → ∀ (k : ℕ), 0 < k →
        ∀ v : CStarMatrix (Fin k) (Fin k) A,
          star v * v = 1 → v * star v = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ _countableG
    exact (canonicalFaithfulTracialState G).map_star_mul_self_eq_zero_iff
  · intro A _ tau I _ _ hI v hv
    exact tau.matrix_mul_star_eq_one_of_star_mul_eq_one I hI hv
  · intro A _ tau k hk v hv
    exact tau.matrix_mul_star_eq_one_of_star_mul_eq_one
      (Fin k) ⟨⟨0, hk⟩⟩ hv

/-! ## Closed forms of directly cited declarations

The zero-input gate requires every manuscript-cited declaration to be a
closed proposition: every binder after the colon.  The declarations
below restate library theorems whose natural homes carry telescope
binders. -/

/-- Closed form of the invariant-size principle: a conjugation-invariant
`ℕ`-valued size on subgroups under which equal-size inclusions are
equalities admits no strict one-sided compression. -/
theorem manuscriptInvariantSizePrinciple :
    ∀ {Q : Type u} [Group Q] (size : Subgroup Q → ℕ),
      (∀ (g : Q) (K : Subgroup Q),
        size (K.map (MulAut.conj g).toMonoidHom) = size K) →
      (∀ K L : Subgroup Q, K ≤ L → size L ≤ size K → K = L) →
      ∀ (K : Subgroup Q) (g : Q),
        K.map (MulAut.conj g).toMonoidHom ≤ K →
        K.map (MulAut.conj g).toMonoidHom = K := by
  intro Q _ size hconj hsep K g hcomp
  exact no_strict_compression_of_invariantSize size hconj hsep K g hcomp

/-- Closed form of the involutive collapse theorem: the involutive
collapse defect of a Kazhdan subgroup with a one-sided compressor lies
in the literal MF radical. -/
theorem manuscriptInvolutiveCollapse :
    ∀ {H : Type} [Group H] [Countable H]
      (L : Subgroup H), HasKazhdanPropertyT.{0, 0} ↥L →
      ∀ (s : H), (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      InvolutionCollapseEndpoint.involutiveCollapseDefect L s ≤
        actualCoronaMFResidual H := by
  intro H _ _ L hT s hcomp
  exact InvolutionCollapseEndpoint.involutiveCollapseDefect_le_actualCoronaMFResidual
    hT hcomp

/-- Closed form of the unconditional radical reduction: the literal MF
radical is the full preimage of the radical of the quotient by any
normal subgroup contained in it. -/
theorem manuscriptRadicalReductionToQuotient :
    ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal],
      N ≤ actualCoronaMFResidual G →
      actualCoronaMFResidual G =
        (actualCoronaMFResidual (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  intro G _ N _ hN
  exact TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient N hN

/-- Closed form of the intrinsic normal-Kazhdan radical theorem. -/
theorem manuscriptIntrinsicNormalKazhdanRadical :
    ∀ {Gamma H : Type} [Group Gamma] [Group H] [Countable H]
      (iota : Gamma →* H),
      HasKazhdanPropertyT.{0, 0} Gamma →
      ∀ (K : Subgroup H) [K.Normal],
        HasKazhdanPropertyT.{0, 0} K →
        K ≤ compressionCentralizerDefect iota.range →
        K ≤ actualCoronaMFResidual H := by
  intro Gamma H _ _ _ iota hkazhdan K _ hT hK
  exact KazhdanAsymptoticCommutant.normalKazhdan_le_actualCoronaMFResidual_of_le_compressionCentralizerDefect
    iota hkazhdan K hT hK

/-- Closed form of the normal Kazhdan part of the intrinsic defect. -/
theorem manuscriptIntrinsicNormalKazhdanPart :
    ∀ {Gamma H : Type} [Group Gamma] [Group H] [Countable H]
      (iota : Gamma →* H),
      HasKazhdanPropertyT.{0, 0} Gamma →
      normalKazhdanPart (compressionCentralizerDefect iota.range) ≤
        actualCoronaMFResidual H := by
  intro Gamma H _ _ _ iota hkazhdan
  exact KazhdanAsymptoticCommutant.normalKazhdanPart_compressionCentralizerDefect_le_actualCoronaMFResidual
    iota hkazhdan

/-! ## The involutive collapse and defect saturation -/

/-- Exact wrapper for the involutive-collapse data: the witness predicate
is literally the displayed three conditions, and the involutive collapse
defect is literally the normal closure of the displayed commutator set,
normal in the ambient group. -/
theorem manuscriptInvolutiveCollapsePattern :
    ∀ {H : Type} [Group H] (L : Subgroup H) (s : H),
    (∀ k : H,
      InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness L s k ↔
        (k * k = 1 ∧ (∀ γ ∈ L, Commute (s * γ * s⁻¹) k) ∧
          (∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
            Commute (γ₁ * k * γ₁⁻¹) (γ₂ * k * γ₂⁻¹)))) ∧
      InvolutionCollapseEndpoint.involutiveCollapseDefect L s =
        Subgroup.normalClosure
          {x | ∃ k : H,
            InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness L s k ∧
            ∃ γ ∈ L, x = ⁅γ, k⁆} ∧
      (InvolutionCollapseEndpoint.involutiveCollapseDefect L s).Normal := by
  intro H _ L s
  exact ⟨fun k ↦ Iff.rfl, rfl, inferInstance⟩

/-- Exact wrapper for the collapse radical reduction: unconditionally the
literal MF radical is the full preimage of the radical of the collapse
quotient, and it equals the collapse defect exactly when the quotient is
operator-MF. -/
theorem manuscriptCollapseRadicalReduction :
    ∀ {H : Type} [Group H] [Countable H]
      (L : Subgroup H) (s : H),
      HasKazhdanPropertyT.{0, 0} ↥L →
      (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      letI : Countable
          (H ⧸ InvolutionCollapseEndpoint.involutiveCollapseDefect L s) :=
        Function.Surjective.countable
          (QuotientGroup.mk'_surjective
            (InvolutionCollapseEndpoint.involutiveCollapseDefect L s))
      actualCoronaMFResidual H =
        (actualCoronaMFResidual
          (H ⧸ InvolutionCollapseEndpoint.involutiveCollapseDefect L s)).comap
          (QuotientGroup.mk'
            (InvolutionCollapseEndpoint.involutiveCollapseDefect L s)) ∧
      (IsCDEOperatorMF
          (H ⧸ InvolutionCollapseEndpoint.involutiveCollapseDefect L s) →
        actualCoronaMFResidual H =
          InvolutionCollapseEndpoint.involutiveCollapseDefect L s) := by
  intro H _ _ L s hT hcomp
  exact
    ⟨InvolutionCollapseEndpoint.actualCoronaMFResidual_eq_comap_involutive_quotient
        hT hcomp,
      fun hquot ↦
        InvolutionCollapseEndpoint.actualCoronaMFResidual_eq_involutiveCollapseDefect
          hT hcomp hquot⟩

/-- Exact wrapper for defect saturation: the collapse defect dies in every
homomorphism to a countable operator-MF group, and a saturated defect
forces the full literal MF radical, trivializes every homomorphism to a
countable operator-MF group, and rules out operator-MF approximation of a
nontrivial ambient group. -/
theorem manuscriptDefectSaturation :
    ∀ {H : Type} [Group H] [Countable H]
      (L : Subgroup H) (s : H),
      HasKazhdanPropertyT.{0, 0} ↥L →
      (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
    (∀ {Q : Type} [Group Q] [Countable Q] (f : H →* Q),
        IsCDEOperatorMF Q →
        InvolutionCollapseEndpoint.involutiveCollapseDefect L s ≤ f.ker) ∧
      (InvolutionCollapseEndpoint.involutiveCollapseDefect L s = ⊤ →
        actualCoronaMFResidual H = ⊤ ∧
        (∀ {Q : Type} [Group Q] [Countable Q] (f : H →* Q),
          IsCDEOperatorMF Q → ∀ x : H, f x = 1) ∧
        (Nontrivial H → ¬ IsCDEOperatorMF H)) := by
  intro H _ _ L s hT hcomp
  constructor
  · intro Q _ _ f hQ
    exact DefectSaturation.involutiveCollapseDefect_le_ker_of_isCDEOperatorMF
      hT hcomp f hQ
  · intro hsat
    refine ⟨DefectSaturation.actualCoronaMFResidual_eq_top_of_saturated
        hT hcomp hsat, ?_, ?_⟩
    · intro Q _ _ f hQ x
      exact DefectSaturation.map_eq_one_of_saturated hT hcomp hsat f hQ x
    · intro hNontrivial
      letI := hNontrivial
      exact DefectSaturation.not_isCDEOperatorMF_of_saturated hT hcomp hsat

/-! ## The abstract obstruction over an invisible subgroup -/

/-- Exact wrapper for the abstract normal-Kazhdan obstruction: if every
element of `D` is killed in the tracial ultraproduct attached to every
operator-norm almost representation, then every normal property-`(T)`
subgroup of `D` dies in every norm matrix C*-corona representation, for
literal positive natural matrix dimensions. -/
/-- Manuscript Definition (Hilbert--Schmidt invisibility): the element
is killed in the tracial ultraproduct attached to every operator-norm
almost representation, along every ultrafilter refining the cofinite
filter.  This is the per-element form of the hypothesis of the abstract
invisibility obstruction below. -/
def ManuscriptHSInvisible {H : Type} [Group H] (g : H) : Prop :=
  ∀ (B : OpAlmostRepresentation H) (U : Ultrafilter ℕ)
    (hcof : (U : Filter ℕ) ≤ Filter.cofinite),
    (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
      hcof g = 1

theorem manuscriptAbstractNormalKazhdanObstruction :
    ∀ {H : Type} [Group H] [Countable H]
      (D : Subgroup H)
      (hDkill : ∀ (B : OpAlmostRepresentation H) (U : Ultrafilter ℕ)
        (hcof : (U : Filter ℕ) ≤ Filter.cofinite) (x : H), x ∈ D →
        (KazhdanCompressionCore.toAsymptoticUnitaryRepresentation B).toUltraproductHom
          hcof x = 1)
      (K : Subgroup H) [K.Normal]
      (hT : HasKazhdanPropertyT.{0, 0} K)
      (hK : K ≤ D)
      (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa [X] using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      K ≤ Theta.ker := by
  intro H _ _ D hDkill K _ hT hK d hd
  exact KazhdanCompressionCore.normalKazhdan_le_normMatrixCStarCoronaKernel_of_hyperlinear_killed
    D hDkill K hT hK
    (fun n ↦ naturalFiniteModel (d n)) (fun n ↦ by
      simpa using hd n)

end

end ManuscriptExactWrappers
end GroupApproximation
