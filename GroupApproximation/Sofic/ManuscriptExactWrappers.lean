import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Monsters.CliffordAlgebraLamp
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.FiniteNormalAverageCorner
import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
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
theorem manuscriptMFDefinitionEquivalences
    (G : Type u) [Group G] [Countable G] :
    (IsCDEOperatorMF G ↔ IsOperatorMF G) ∧
      (IsOperatorMF G ↔ IsNormApproximable G 1) ∧
      (IsOperatorMFIncreasing G ↔ IsOperatorMF G) := by
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
      (∀ (k : Type u) (V : Type v) (H : Type w)
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
theorem manuscriptCliffordConstruction (X : Type u) :
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
theorem manuscriptUnitaryLifting
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa using hd n)
    ∀ x : unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      ∃ u : ∀ n, Matrix.unitaryGroup (X n) ℂ,
        unitarySequenceToCorona X u = x := by
  intro x
  obtain ⟨q, hq⟩ := unitaryCoronaToCStarCoronaUnitary_surjective X x
  induction q using Quotient.inductionOn with
  | _ u => exact ⟨u, by simpa using hq⟩

/-- The canonical unitary-sequence/C-star-corona isomorphism, including its
formula on every represented sequence. -/
theorem manuscriptUnitaryCoronaEquivalence
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa using hd n)
    ∃ kappa : NormMatrixCoronaUnitary X ≃*
        unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      kappa.toMonoidHom = unitaryCoronaToCStarCoronaUnitary X ∧
        ∀ u : ∀ n, Matrix.unitaryGroup (X n) ℂ,
          kappa (QuotientGroup.mk u) = unitarySequenceToCorona X u := by
  exact ⟨normMatrixCoronaUnitaryEquiv X, rfl,
    unitaryCoronaToCStarCoronaUnitary_mk X⟩

/-- Exact data and defect subgroup of a marked Kazhdan pattern. -/
theorem manuscriptMarkedKazhdanPattern
    {Gamma : Type} {H : Type u} [Group Gamma] [Group H]
    [_countableGamma : Countable Gamma] [_countableH : Countable H]
    (C : KazhdanCompressionCore Gamma H) :
    HasKazhdanPropertyT.{0, 0} Gamma ∧
      HasKazhdanPropertyTComplex.{0, w} Gamma ∧
      (∀ gamma : Gamma, ∃ delta : Gamma,
        C.t * C.iota gamma * C.t⁻¹ = C.iota delta) ∧
      (∀ gamma : Gamma, Commute C.c (C.iota gamma)) ∧
      C.defectNormal = Subgroup.normalClosure
        (Set.range fun gamma : Gamma ↦
          ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆) ∧
      C.defectNormal.Normal := by
  exact ⟨C.kazhdan, hasKazhdanPropertyT_iff_textbook.mp C.kazhdan,
    C.compresses, C.comm_c, rfl, inferInstance⟩

/-- Exact natural-dimension form of the finite-normal obstruction criterion:
every homomorphism into the unitary group of the genuine norm-matrix C-star
corona maps the specified finite normal subgroup to the identity. -/
theorem manuscriptFiniteNormalObstructionCriterion
    {Gamma : Type} {H : Type u} [Group Gamma] [Group H]
    [_countableGamma : Countable Gamma] [Countable H]
    (C : KazhdanCompressionCore Gamma H)
    (F : Subgroup H) [Finite F] [F.Normal]
    (hF : F ≤ C.defectNormal)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    let X : ℕ → FiniteModel := fun n ↦ naturalFiniteModel (d n)
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (by
        simpa using hd n)
    ∀ Theta : H →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      F ≤ Theta.ker := by
  exact C.finiteNormal_le_normMatrixCStarCoronaKernel F hF
    (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd)

/-- Exact coordinate finite-normal-corner conclusion for literal positive
natural matrix dimensions. -/
theorem manuscriptCoordinateFiniteNormalCorner
    {H : Type u} [Group H] [Countable H]
    (F : Subgroup H) [Finite F] [F.Normal]
    {I : Type} (U : Ultrafilter I) (d : I → ℕ)
    (hd : ∀ i, 0 < d i)
    (rho : H →* UniversalWeakMF U (fun i ↦ naturalFiniteModel (d i)))
    (hnontrivial : ∃ f : F, rho f ≠ 1) :
    ∃ B : OpAlmostRepresentation H,
      (∀ n, 0 < Fintype.card (B.model n)) ∧
      (∀ g h : H, ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
        ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h -
          (B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ)‖ ≤
            epsilon) ∧
      letI : Fintype F := Fintype.ofFinite F
      KazhdanCornerMatrices.OpNormVanishing B (fun n ↦
        ∑ f : F, (B.map n (f : H) :
          Matrix (B.model n) (B.model n) ℂ)) := by
  letI : ∀ i, Nonempty (naturalFiniteModel (d i)) := fun i ↦
    Fintype.card_pos_iff.mp (by simpa using hd i)
  obtain ⟨B, hsum⟩ :=
    FiniteNormalAverageCorner.exists_corner_with_finite_sum_vanishing
      F U (fun i ↦ naturalFiniteModel (d i)) rho hnontrivial
  refine ⟨B, B.modelNonempty, ?_, hsum⟩
  intro g h epsilon hepsilon
  obtain ⟨N, hN⟩ := B.asymptoticallyMultiplicative g h epsilon hepsilon
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    ‖(B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h -
        (B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ)‖ =
        ‖-((B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)‖ := by
            rw [neg_sub]
    _ = ‖(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ) -
          (B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h‖ :=
        norm_neg _
    _ ≤ epsilon := hN n hn

/-- Exact outer-form version of the manuscript's compression-defect collapse:
the squared normalized Hilbert--Schmidt distance tends to zero, which is
equivalent to convergence of the normalized Hilbert--Schmidt norm itself. -/
theorem manuscriptCompressionDefectsCollapse
    {Gamma : Type} {H : Type u} [Group Gamma] [Group H]
    [Countable Gamma] [Countable H]
    (C : KazhdanCompressionCore Gamma H)
    (B : OpAlmostRepresentation H) :
    ∀ gamma : Gamma, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N, ∀ n ≥ N,
        hsDistSq (B.model n)
          (B.map n
            ⁅C.t * C.c * C.t⁻¹, C.iota gamma⁆)
          (B.map n 1) ≤ epsilon := by
  simpa [KazhdanCompressionCore.transported] using
    C.compressionDefects_hsTrivial B

/-! ## MF radical and quotient -/

/-- The MF radical is literally the intersection-of-kernels predicate and is
a normal subgroup. -/
theorem manuscriptMFRadical
    (G : Type u) [Group G] [_countableG : Countable G] :
    ((∀ x : G, x ∈ manuscriptCoronaMFResidual G ↔
      ∀ (d : ℕ → ℕ), ∀ hd : ∀ n, 0 < d n,
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : G →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          rho x = 1)) ∧
      (manuscriptCoronaMFResidual G).Normal := by
  exact ⟨fun _ ↦ Iff.rfl, inferInstance⟩

/-- Functoriality of the MF radical together with the literal marked-word
consequence printed in the portability lemma. -/
theorem manuscriptRadicalPortability
    (G1 : Type u) [Group G1] [_countableG1 : Countable G1]
    (G2 : Type v) [Group G2] [Countable G2] :
    (∀ f : G1 →* G2,
      (manuscriptCoronaMFResidual G1).map f ≤ manuscriptCoronaMFResidual G2) ∧
      (∀ (phi : MarkedGroup →* G2),
        phi mark ≠ 1 →
          mark ∈ manuscriptCoronaMFResidual MarkedGroup →
            ¬ IsCDEOperatorMF G2) := by
  constructor
  · exact map_manuscriptCoronaMFResidual_le
  · intro phi hsurvive hmark hMF
    have himage : phi mark ∈ manuscriptCoronaMFResidual G2 :=
      map_manuscriptCoronaMFResidual_le phi ⟨mark, hmark, rfl⟩
    have hbot : manuscriptCoronaMFResidual G2 = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
    rw [hbot] at himage
    exact hsurvive (Subgroup.mem_bot.mp himage)

/-- All clauses of the largest-MF-quotient proposition, using the literal
CDE definition at the public boundary. -/
theorem manuscriptLargestMFQuotient
    (G : Type u) [Group G] [Countable G] :
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
  refine
    ⟨exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual,
      manuscriptCoronaMFQuotient_isCDEOperatorMF, ?_, ?_⟩
  · intro H _ _ f hH
    exact
      (existsUnique_manuscriptCoronaMFQuotient_factorization_to_isCDEOperatorMF
        f hH).exists
  · exact isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot

/-- Exact factorization and equality criterion for a proposed radical. -/
theorem manuscriptExactRadicalFromCandidateQuotient
    (G : Type u) [Group G] [Countable G]
    (N : Subgroup G) [N.Normal] (hN : N ≤ manuscriptCoronaMFResidual G) :
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
      (∀ (A : Type u) [CStarAlgebra A]
        (tau : FaithfulTracialState A)
        (I : Type*) [Fintype I] [DecidableEq I], Nonempty I →
        ∀ v : CStarMatrix I I A,
          star v * v = 1 → v * star v = 1) ∧
      (∀ (A : Type u) [CStarAlgebra A]
        (tau : FaithfulTracialState A) (k : ℕ), 0 < k →
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

end

end ManuscriptExactWrappers
end GroupApproximation
