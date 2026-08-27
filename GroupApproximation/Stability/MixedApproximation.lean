import GroupApproximation.Sofic.KazhdanCornerMatrices
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.SoficPositiveControl
import GroupApproximation.Sofic.SoficUltraproduct
import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Mixed Hamming/operator-norm approximation and stability

This file formalizes the abstract part of the simultaneous-stability argument.
The mixed approximation class is the union of sofic groups and operator-MF
groups.  A group with no nontrivial quotient in that union has a much stronger
property than ordinary pointwise stability: every permutation or
operator-norm almost representation converges pointwise to the trivial
representation.

The proof is internal.  A permutation almost representation is read in a
Hamming ultraproduct chosen through any hypothetical infinite bad set.  An
operator-norm almost representation is read in the cofinite norm-matrix
corona.  Both targets belong to the relevant approximation class, so the
induced homomorphism must be trivial.

This module makes no conditional existence claim.  The external
Fournier--Facio construction is not represented by an axiom, typeclass,
structure field, or theorem-shaped hypothesis.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

/-! ## The mixed approximation class -/

/-- Approximation by either finite symmetric groups in normalized Hamming
distance or finite-dimensional unitary groups in operator norm. -/
def IsMixedApproximable (G : Type u) [Group G] : Prop :=
  IsSofic G ∨ IsOperatorMF G

/-- The direct product of a nonsofic group and a non-operator-MF group is not
approximable by the mixed family.  This is the formal form of the subsequence
argument: membership in the union would put one of the two factors in its
forbidden class by subgroup permanence. -/
theorem not_isMixedApproximable_prod
    {Q W : Type*} [Group Q] [Group W]
    (hQ : ¬ IsSofic Q) (hW : ¬ IsOperatorMF W) :
    ¬ IsMixedApproximable (Q × W) := by
  rintro (hS | hMF)
  · exact hQ (isSofic_of_injective (MonoidHom.inl Q W)
      (fun _ _ h ↦ congrArg Prod.fst h) hS)
  · exact hW (hMF.comap (MonoidHom.inr Q W)
      (fun _ _ h ↦ congrArg Prod.snd h))

/-- A subgroup of a mixed-approximable group is mixed-approximable. -/
theorem IsMixedApproximable.subgroup {G : Type*} [Group G]
    (hG : IsMixedApproximable G) (H : Subgroup G) :
    IsMixedApproximable H := by
  rcases hG with hG | hG
  · exact Or.inl (isSofic_of_injective H.subtype Subtype.val_injective hG)
  · exact Or.inr (hG.subgroup H)

/-! ## No nontrivial mixed quotient -/

/-- Every surjection from `G` onto a mixed-approximable group has trivial
target.  Quantifying over surjections is a universe-safe, literal formulation
of "no nontrivial mixed-approximable quotient" for the concrete groups used
below. -/
def HasNoNontrivialMixedQuotient (G : Type*) [Group G] : Prop :=
  ∀ (H : Type) [Group H], IsMixedApproximable H →
    ∀ f : G →* H, Function.Surjective f → Subsingleton H

/-- Every sofic quotient is trivial. -/
def HasNoNontrivialSoficQuotient (G : Type*) [Group G] : Prop :=
  ∀ (H : Type) [Group H], IsSofic H →
    ∀ f : G →* H, Function.Surjective f → Subsingleton H

/-- Every operator-MF quotient is trivial. -/
def HasNoNontrivialOperatorMFQuotient (G : Type*) [Group G] : Prop :=
  ∀ (H : Type) [Group H], IsOperatorMF H →
    ∀ f : G →* H, Function.Surjective f → Subsingleton H

/-- Every finite quotient is trivial. -/
def HasNoNontrivialFiniteQuotient (G : Type*) [Group G] : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    ∀ f : G →* K, Function.Surjective f → Subsingleton K

namespace HasNoNontrivialMixedQuotient

variable {G : Type} [Group G]

/-- The range of a homomorphism to a mixed-approximable group is a mixed
approximable quotient of the source. -/
theorem hom_eq_one (hG : HasNoNontrivialMixedQuotient G)
    {H : Type} [Group H] (hH : IsMixedApproximable H) (f : G →* H) :
    f = 1 := by
  have hRange : IsMixedApproximable f.range := hH.subgroup f.range
  letI : Subsingleton f.range :=
    hG f.range hRange f.rangeRestrict f.rangeRestrict_surjective
  ext g
  have h : f.rangeRestrict g = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- In particular, every homomorphism from `G` to a sofic group is trivial. -/
theorem hom_eq_one_of_isSofic (hG : HasNoNontrivialMixedQuotient G)
    {H : Type} [Group H] (hH : IsSofic H) (f : G →* H) : f = 1 :=
  hG.hom_eq_one (Or.inl hH) f

/-- In particular, every homomorphism from `G` to an operator-MF group is
trivial. -/
theorem hom_eq_one_of_isOperatorMF
    (hG : HasNoNontrivialMixedQuotient G)
    {H : Type} [Group H] (hH : IsOperatorMF H) (f : G →* H) : f = 1 :=
  hG.hom_eq_one (Or.inr hH) f

/-- A nontrivial group with no nontrivial mixed quotient is nonsofic. -/
theorem not_isSofic (hG : HasNoNontrivialMixedQuotient G)
    [Nontrivial G] : ¬ IsSofic G := by
  intro hS
  exact not_subsingleton G
    (hG G (Or.inl hS) (MonoidHom.id G) Function.surjective_id)

/-- A nontrivial group with no nontrivial mixed quotient is not operator-MF. -/
theorem not_isOperatorMF (hG : HasNoNontrivialMixedQuotient G)
    [Nontrivial G] : ¬ IsOperatorMF G := by
  intro hMF
  exact not_subsingleton G
    (hG G (Or.inr hMF) (MonoidHom.id G) Function.surjective_id)

/-- Every homomorphism from `G` to a finite group is trivial. -/
theorem finite_hom_eq_one (hG : HasNoNontrivialMixedQuotient G)
    {K : Type} [Group K] [Finite K] (f : G →* K) : f = 1 :=
  hG.hom_eq_one_of_isSofic (isSofic_of_finite' K) f

/-- Hence every finite quotient is trivial. -/
theorem finite_quotient_subsingleton
    (hG : HasNoNontrivialMixedQuotient G)
    {K : Type} [Group K] [Finite K] (f : G →* K)
    (hf : Function.Surjective f) : Subsingleton K :=
  hG K (Or.inl (isSofic_of_finite' K)) f hf

/-- The mixed statement contains the no-sofic-quotient statement. -/
theorem hasNoNontrivialSoficQuotient
    (hG : HasNoNontrivialMixedQuotient G) :
    HasNoNontrivialSoficQuotient G := by
  intro H _ hH f hf
  exact hG H (Or.inl hH) f hf

/-- The mixed statement contains the no-operator-MF-quotient statement. -/
theorem hasNoNontrivialOperatorMFQuotient
    (hG : HasNoNontrivialMixedQuotient G) :
    HasNoNontrivialOperatorMFQuotient G := by
  intro H _ hH f hf
  exact hG H (Or.inr hH) f hf

/-- The mixed statement contains the no-finite-quotient statement. -/
theorem hasNoNontrivialFiniteQuotient
    (hG : HasNoNontrivialMixedQuotient G) :
    HasNoNontrivialFiniteQuotient G := by
  intro K _ _ f hf
  exact hG.finite_quotient_subsingleton f hf

/-- Every nontrivial quotient is simultaneously nonsofic and
non-operator-MF. -/
theorem nontrivial_quotient_not_sofic_and_not_operatorMF
    (hG : HasNoNontrivialMixedQuotient G)
    {H : Type} [Group H] [Nontrivial H] (f : G →* H)
    (hf : Function.Surjective f) : ¬ IsSofic H ∧ ¬ IsOperatorMF H := by
  constructor
  · intro hH
    exact not_subsingleton H (hG H (Or.inl hH) f hf)
  · intro hH
    exact not_subsingleton H (hG H (Or.inr hH) f hf)

/-- The no-mixed-quotient property passes to quotients. -/
theorem of_surjective (hG : HasNoNontrivialMixedQuotient G)
    {L : Type} [Group L] (q : G →* L) (hq : Function.Surjective q) :
    HasNoNontrivialMixedQuotient L := by
  intro H _ hH f hf
  exact hG H hH (f.comp q) (hf.comp hq)

/-- An infinite group with no nontrivial finite quotient is not residually
finite. -/
theorem not_residuallyFinite (hG : HasNoNontrivialMixedQuotient G)
    [Infinite G] : ¬ Group.ResiduallyFinite G := by
  intro hRF
  letI : Group.ResiduallyFinite G := hRF
  apply not_subsingleton G
  refine ⟨fun g h ↦ ?_⟩
  have hall : ∀ x : G, x = 1 := by
    intro x
    apply Group.eq_one_iff_forall_finiteIndexNormalSubroup x
    intro N
    let π : G →* G ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
    have hπ : π = 1 := hG.finite_hom_eq_one π
    apply (QuotientGroup.eq_one_iff _).mp
    have hx := DFunLike.congr_fun hπ x
    simpa [π] using hx
  exact (hall g).trans (hall h).symm

end HasNoNontrivialMixedQuotient

/-! ## Pointwise Hamming stability -/

/-- A sequence of finite permutation-valued maps with pointwise vanishing
multiplicative defect.  Unlike `SoficApproximation`, no separation or growth
condition is imposed. -/
structure HammingAlmostRepresentation (G : Type*) [Group G] where
  model : ℕ → FiniteModel
  modelNonempty : ∀ n, 0 < Fintype.card (model n)
  map : ∀ n, G → Equiv.Perm (model n)
  asymptoticallyMultiplicative : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    hammingDistance (model n) (map n (g * h)) (map n g * map n h) < ε

namespace HammingAlmostRepresentation

variable {G : Type} [Group G]

/-- The homomorphism into a Hamming ultraproduct induced by an almost
representation along an ultrafilter extending the cofinite filter. -/
noncomputable def ultraproductHom (A : HammingAlmostRepresentation G)
    (𝒰 : Ultrafilter ℕ) (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    G →* UniversalSofic 𝒰 A.model := by
  have hnull : ∀ g h : G,
      (fun n ↦ A.map n g * A.map n h)⁻¹ * (fun n ↦ A.map n (g * h)) ∈
        nullSubgroup 𝒰 A.model := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h ε hε
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    change hammingLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < ε
    rw [hammingLength_inv_mul]
    exact hN n hn
  exact MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g))
    (fun g h ↦ by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq.mpr (hnull g h)).symm)

/-- Pointwise convergence of an almost representation to the trivial
representation. -/
def IsAsymptoticallyTrivial (A : HammingAlmostRepresentation G) : Prop :=
  ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    hammingDistance (A.model n) (A.map n g) 1 < ε

end HammingAlmostRepresentation

/-- Pointwise permutation stability: every permutation almost representation
is pointwise close to a sequence of genuine actions on the same finite sets. -/
def IsPointwisePStable (G : Type*) [Group G] : Prop :=
  ∀ A : HammingAlmostRepresentation G,
    ∃ ρ : ∀ n, G →* Equiv.Perm (A.model n),
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        hammingDistance (A.model n) (A.map n g) (ρ n g) < ε

/-- Absence of nontrivial mixed quotients forces every permutation almost
representation to converge pointwise to the trivial action. -/
theorem HasNoNontrivialMixedQuotient.hammingAlmostRepresentation_trivial
    {G : Type} [Group G] (hG : HasNoNontrivialMixedQuotient G)
    (A : HammingAlmostRepresentation G) : A.IsAsymptoticallyTrivial := by
  intro g ε hε
  by_contra hclose
  push Not at hclose
  have hfrequent : ∃ᶠ n in Filter.cofinite,
      ε ≤ hammingDistance (A.model n) (A.map n g) 1 := by
    rw [Nat.cofinite_eq_atTop, Filter.frequently_atTop]
    exact hclose
  let bad : Set ℕ :=
    {n | ε ≤ hammingDistance (A.model n) (A.map n g) 1}
  let F : Filter ℕ := Filter.cofinite ⊓ Filter.principal bad
  have hF : F.NeBot := by
    exact Filter.frequently_iff_neBot.mp hfrequent
  letI : F.NeBot := hF
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of F
  have h𝒰F : (𝒰 : Filter ℕ) ≤ F := Ultrafilter.of_le F
  have hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite :=
    h𝒰F.trans inf_le_left
  have hbad : ∀ᶠ n in (𝒰 : Filter ℕ),
      ε ≤ hammingDistance (A.model n) (A.map n g) 1 := by
    exact Filter.le_principal_iff.mp (h𝒰F.trans inf_le_right)
  let ρ : G →* UniversalSofic 𝒰 A.model := A.ultraproductHom 𝒰 hcof
  have hTarget : IsSofic (UniversalSofic 𝒰 A.model) :=
    isSofic_of_soficEmbedding 𝒰 A.model A.modelNonempty
      (MonoidHom.id _) Function.injective_id
  have hρ : ρ = 1 := hG.hom_eq_one_of_isSofic hTarget ρ
  have heq :
      (QuotientGroup.mk (fun n ↦ A.map n g) : UniversalSofic 𝒰 A.model) = 1 := by
    simpa [ρ, HammingAlmostRepresentation.ultraproductHom] using
      DFunLike.congr_fun hρ g
  have hnull : (fun n ↦ A.map n g) ∈ nullSubgroup 𝒰 A.model :=
    (QuotientGroup.eq_one_iff _).mp heq
  have hsmall : ∀ᶠ n in (𝒰 : Filter ℕ),
      hammingDistance (A.model n) (A.map n g) 1 < ε := by
    simpa only [hammingLength] using hnull ε hε
  obtain ⟨n, hnfar, hnclose⟩ := (hbad.and hsmall).exists
  exact (not_lt_of_ge hnfar) hnclose

/-- Therefore no nontrivial mixed quotient implies pointwise P-stability,
witnessed by the trivial actions. -/
theorem HasNoNontrivialMixedQuotient.isPointwisePStable
    {G : Type} [Group G] (hG : HasNoNontrivialMixedQuotient G) :
    IsPointwisePStable G := by
  intro A
  refine ⟨fun _ ↦ 1, ?_⟩
  intro g ε hε
  obtain ⟨N, hN⟩ := hG.hammingAlmostRepresentation_trivial A g ε hε
  exact ⟨N, fun n hn ↦ by simpa using hN n hn⟩

/-! ## Pointwise operator-norm stability -/

namespace OpAlmostRepresentation

variable {G : Type} [Group G]

/-- The homomorphism into the cofinite norm-matrix corona induced by an
operator-norm almost representation. -/
noncomputable def coronaHom (A : OpAlmostRepresentation G) :
    G →* NormMatrixCoronaUnitary A.model := by
  have hnull : ∀ g h : G,
      (fun n ↦ A.map n g * A.map n h)⁻¹ * (fun n ↦ A.map n (g * h)) ∈
        nullCofiniteOpSubgroup A.model := by
    intro g h ε hε
    obtain ⟨N, hN⟩ :=
      A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with n hn
    change opLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < ε
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  exact MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g))
    (fun g h ↦ by
      rw [← QuotientGroup.mk_mul]
      exact (QuotientGroup.eq.mpr (hnull g h)).symm)

/-- Pointwise convergence of an operator-norm almost representation to the
trivial representation. -/
def IsAsymptoticallyTrivial (A : OpAlmostRepresentation G) : Prop :=
  ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1‖ < ε

end OpAlmostRepresentation

/-- Pointwise operator-norm matricial stability on the same matrix sizes. -/
def IsPointwiseOperatorNormStable (G : Type*) [Group G] : Prop :=
  ∀ A : OpAlmostRepresentation G,
    ∃ ρ : ∀ n, G →* Matrix.unitaryGroup (A.model n) ℂ,
      ∀ g : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - ρ n g‖ < ε

/-- A positive sequence of matrix sizes makes its own cofinite norm-matrix
corona operator-MF, via the identity embedding. -/
theorem normMatrixCoronaUnitary_isOperatorMF (X : ℕ → FiniteModel)
    (hX : ∀ n, 0 < Fintype.card (X n)) :
    IsOperatorMF (NormMatrixCoronaUnitary X) :=
  ⟨X, hX, MonoidHom.id _, Function.injective_id⟩

/-- Absence of nontrivial mixed quotients forces every operator-norm almost
representation to converge pointwise to the trivial representation. -/
theorem HasNoNontrivialMixedQuotient.opAlmostRepresentation_trivial
    {G : Type} [Group G] (hG : HasNoNontrivialMixedQuotient G)
    (A : OpAlmostRepresentation G) : A.IsAsymptoticallyTrivial := by
  intro g ε hε
  let ρ : G →* NormMatrixCoronaUnitary A.model := A.coronaHom
  have hρ : ρ = 1 := hG.hom_eq_one_of_isOperatorMF
    (normMatrixCoronaUnitary_isOperatorMF A.model A.modelNonempty) ρ
  have heq :
      (QuotientGroup.mk (fun n ↦ A.map n g) : NormMatrixCoronaUnitary A.model) = 1 := by
    simpa [ρ, OpAlmostRepresentation.coronaHom] using DFunLike.congr_fun hρ g
  have hnull : (fun n ↦ A.map n g) ∈ nullCofiniteOpSubgroup A.model :=
    (QuotientGroup.eq_one_iff _).mp heq
  have hsmall := hnull ε hε
  rw [Nat.cofinite_eq_atTop] at hsmall
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa only [opLength] using hN n hn

/-- Therefore no nontrivial mixed quotient implies pointwise operator-norm
matricial stability, witnessed by the trivial representations. -/
theorem HasNoNontrivialMixedQuotient.isPointwiseOperatorNormStable
    {G : Type} [Group G] (hG : HasNoNontrivialMixedQuotient G) :
    IsPointwiseOperatorNormStable G := by
  intro A
  refine ⟨fun _ ↦ 1, ?_⟩
  intro g ε hε
  obtain ⟨N, hN⟩ := hG.opAlmostRepresentation_trivial A g ε hε
  exact ⟨N, fun n hn ↦ by simpa using hN n hn⟩

end GroupApproximation
