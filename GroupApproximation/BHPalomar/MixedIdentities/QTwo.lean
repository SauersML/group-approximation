import GroupApproximation.BHPalomar.MixedIdentities.Separation
import GroupApproximation.BHPalomar.MixedIdentities.ThreeArc
import GroupApproximation.GroupTheory.HydeLodha.QTwoStatement
import GroupApproximation.GroupTheory.HydeLodha.FinitelyPresentedInfiniteSimpleClosed
import GroupApproximation.GroupTheory.HydeLodha.GammaTwoStabilizer
import GroupApproximation.Meta.AxiomGuard

/-!
# BFFHZ Question 3.3 at Hyde–Lodha's `Q₂`

Belk–Fournier-Facio–Hyde–Zaremsky (arXiv:2503.21882v2), Question 3.3: for a finitely presented
simple group `G`, are the mixed identities `J_G(G ∗ F_n)` finitely normally generated? The research
answer (`thompson-t-mixed-identities-are-not-finitely-normally-generated`) is no, with Thompson's
`T` as witness. The argument uses only that the group acts on the circle by piecewise-affine
orientation-preserving maps with elements supported in every small arc. Here the witness is
Hyde–Lodha's `Q₂ = [Γ₂, Γ₂]`, which acts that way on `ℚ` modulo `ℤ`. It is already finitely
presented and simple in the repository.

* `isFinitelyPresented_qTwo`, `isSimpleGroup_qTwo_closed`: the witness.
* `exists_qTwo_supportedIn`: `Q₂` has nontrivial elements supported in `perSet (u, v)` for every
  `0 ≤ u < v ≤ 1`. A nontrivial core commutator is conjugated into `(u, v)` by the Higman–Epstein
  room of the core, then made periodic.
* `threeArcWord_mem_mixedIdentities`: the three-arc word is a mixed identity of `Q₂`
  (`threeArc_word_eq_one`).
* `evalPerm P`: the substitution `Q₂ ∗ ⟨x⟩ → Perm ℚ`, `x ↦ P`. The overgroup is the group of
  periodic permutations of `ℚ`, the analogue of `V` for `T`.
* Two dynamical statements are still owed:
  - `SmallSupportCollapseStatement` (part 1 of the research proof): any finite set of mixed
    identities is killed by every periodic permutation supported in some small `perSet (u, v)`;
  - `ThreeArcViolationStatement` (part 2): every such scale carries a periodic permutation that
    breaks some three-arc word.
* `mixedIdentities_statement_of`: the challenge statement from those two.
-/

namespace GroupApproximation
namespace BHPalomar
namespace MixedIdentities

open scoped commutatorElement
open HydeLodha HigmanThompson
open Manuscript.NonMF.TorsionFreePrinted

/-! ## The witness -/

/-- `Q₂` is finitely presented (Hyde–Lodha, Theorem 4.8, closed in the repository). -/
theorem isFinitelyPresented_qTwo : Group.IsFinitelyPresented ↥qTwo :=
  isFinitelyPresented_qTwo_of_stabK
    (stabKFinitelyPresented_of_upsilon (upsilonFinitelyPresented_of_dynamics lemmaFourSixDynamics)
      le_rfl qTwo_le_gammaTwo)

/-- **Small supports.** `Q₂` has a nontrivial element supported in `perSet (u, v)`. -/
theorem exists_qTwo_supportedIn {u v : ℚ} (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) :
    ∃ a : ↥qTwo, a ≠ 1 ∧ SupportedIn (a : Equiv.Perm ℚ) (perSet (Set.Ioo u v)) := by
  obtain ⟨⟨x, hx⟩, hx1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (commutator_compactCore_ne_bot (m := 4))
  have hxc : x ∈ compactCore 4 := commutator_le_self _ hx
  obtain ⟨k, hk, -, -, -, -, U₁, -, -, hs, -, -, -, -, -, -, hsub⟩ :=
    compactCore_room (m := 4) hu huv hv x hxc x hxc
  have hy : k * x * k⁻¹ ∈ ⁅compactCore 4, compactCore 4⁆ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hx) (Subgroup.inv_mem _ hk)
  have hyF : k * x * k⁻¹ ∈ compactF 4 1 := compactCore_le (m := 4) (commutator_le_self _ hy)
  refine ⟨⟨perHom 4 ⟨k * x * k⁻¹, hyF⟩, commutator_perCore_le_qTwo
    (perHom_mem_commutator_perCore (m := 4) (x := ⟨k * x * k⁻¹, hyF⟩) hy)⟩, ?_, ?_⟩
  · intro h1
    have h2 : perHom 4 ⟨k * x * k⁻¹, hyF⟩ = perHom 4 1 := by
      rw [map_one]
      exact congrArg Subtype.val h1
    have h3 := perHom_injective (m := 4) h2
    have h4 : k * x * k⁻¹ = 1 := congrArg Subtype.val h3
    apply hx1
    apply Subtype.ext
    show x = 1
    calc x = k⁻¹ * (k * x * k⁻¹) * k := by group
      _ = 1 := by rw [h4]; group
  · have hs' : SupportedIn (perHom 4 ⟨k * x * k⁻¹, hyF⟩) (perSet U₁) :=
      supportedIn_perHom 4 (f := ⟨k * x * k⁻¹, hyF⟩) hs
    exact hs'.mono (perSet_mono fun t ht => hsub (Or.inl (Or.inl ht)))

/-! ## The three-arc word is a mixed identity of `Q₂` -/

/-- **The three-arc word is a mixed identity of `Q₂`.** -/
theorem threeArcWord_mem_mixedIdentities {a₁ a₂ a₃ : ↥qTwo} {α₁ β₁ α₂ β₂ α₃ β₃ : ℚ}
    (h0 : 0 ≤ α₁) (h12 : β₁ ≤ α₂) (h23 : β₂ ≤ α₃) (h1 : β₃ ≤ 1)
    (ha₁ : SupportedIn (a₁ : Equiv.Perm ℚ) (perSet (Set.Ioo α₁ β₁)))
    (ha₂ : SupportedIn (a₂ : Equiv.Perm ℚ) (perSet (Set.Ioo α₂ β₂)))
    (ha₃ : SupportedIn (a₃ : Equiv.Perm ℚ) (perSet (Set.Ioo α₃ β₃))) :
    threeArcWord a₁ a₂ a₃ ∈ mixedIdentities ↥qTwo 1 := by
  rw [mem_mixedIdentities]
  intro φ hφ
  have hinl : ∀ a : ↥qTwo, φ (Monoid.Coprod.inl a) = a := fun a => DFunLike.congr_fun hφ a
  have hg := (φ (Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)))).2
  apply qTwo.subtype_injective
  simp only [threeArcWord, map_commutatorElement, map_mul, map_inv, hinl, map_one,
    Subgroup.coe_subtype]
  exact threeArc_word_eq_one (gammaTwo_strictMono (qTwo_le_gammaTwo hg))
    (gammaTwo_add_int (qTwo_le_gammaTwo hg)) h0 h12 h23 h1 ha₁ ha₂ ha₃

/-! ## Evaluation in the periodic permutations -/

/-- The substitution `Q₂ ∗ ⟨x⟩ → Perm ℚ` that is the inclusion on `Q₂` and sends `x` to `P`. -/
def evalPerm (P : Equiv.Perm ℚ) : Monoid.Coprod ↥qTwo (FreeGroup (Fin 1)) →* Equiv.Perm ℚ :=
  Monoid.Coprod.lift qTwo.subtype (FreeGroup.lift fun _ => P)

/-- **Part 1 (owed).** Any finite set of mixed identities of `Q₂` is killed by every periodic
permutation supported in some `perSet (u, v)`. Research proof:
`thompson-t-mixed-identities-not-fng-proof`, part 1. At a point avoiding the finitely many fixed
points where a product of constants is not locally the identity, each such product either moves a
small arc off itself or fixes it pointwise. A nontrivial element of `Q₂` supported there, which has
infinite order since `Q₂` is torsion-free, forces every signed count of active letters to vanish. -/
def SmallSupportCollapseStatement : Prop :=
  ∀ W : Set (Monoid.Coprod ↥qTwo (FreeGroup (Fin 1))), W.Finite →
    W ⊆ (mixedIdentities ↥qTwo 1 : Set (Monoid.Coprod ↥qTwo (FreeGroup (Fin 1)))) →
    ∃ u v : ℚ, 0 ≤ u ∧ u < v ∧ v ≤ 1 ∧
      ∀ P : Equiv.Perm ℚ, (∀ t : ℚ, P (t + 1) = P t + 1) →
        SupportedIn P (perSet (Set.Ioo u v)) → ∀ w ∈ W, evalPerm P w = 1

/-- **Part 2 (owed).** At every scale some three-arc word of `Q₂` is broken by a periodic
permutation supported at that scale. Research proof: part 2, generic trajectory plus the extension
of finite partial injections. -/
def ThreeArcViolationStatement : Prop :=
  ∀ u v : ℚ, 0 ≤ u → u < v → v ≤ 1 →
    ∃ a₁ a₂ a₃ : ↥qTwo, ∃ α₁ β₁ α₂ β₂ α₃ β₃ : ℚ,
      0 ≤ α₁ ∧ β₁ ≤ α₂ ∧ β₂ ≤ α₃ ∧ β₃ ≤ 1 ∧
      SupportedIn (a₁ : Equiv.Perm ℚ) (perSet (Set.Ioo α₁ β₁)) ∧
      SupportedIn (a₂ : Equiv.Perm ℚ) (perSet (Set.Ioo α₂ β₂)) ∧
      SupportedIn (a₃ : Equiv.Perm ℚ) (perSet (Set.Ioo α₃ β₃)) ∧
      ∃ P : Equiv.Perm ℚ, (∀ t : ℚ, P (t + 1) = P t + 1) ∧
        SupportedIn P (perSet (Set.Ioo u v)) ∧ evalPerm P (threeArcWord a₁ a₂ a₃) ≠ 1

/-- A mixed identity broken at every scale, from part 2. -/
def ScaleViolationStatement : Prop :=
  ∀ u v : ℚ, 0 ≤ u → u < v → v ≤ 1 →
    ∃ w ∈ mixedIdentities ↥qTwo 1, ∃ P : Equiv.Perm ℚ, (∀ t : ℚ, P (t + 1) = P t + 1) ∧
      SupportedIn P (perSet (Set.Ioo u v)) ∧ evalPerm P w ≠ 1

theorem scaleViolation_of_threeArc (h : ThreeArcViolationStatement) :
    ScaleViolationStatement := by
  intro u v hu huv hv
  obtain ⟨a₁, a₂, a₃, α₁, β₁, α₂, β₂, α₃, β₃, h0, h12, h23, h1, ha₁, ha₂, ha₃, P, hPper, hP,
    hPw⟩ := h u v hu huv hv
  exact ⟨_, threeArcWord_mem_mixedIdentities h0 h12 h23 h1 ha₁ ha₂ ha₃, P, hPper, hP, hPw⟩

/-- **Part 3.** Parts 1 and 2 give that the mixed identities of `Q₂` are not finitely normally
generated in `Q₂ ∗ ℤ`. -/
theorem not_isFinitelyNormallyGenerated_qTwo (h₁ : SmallSupportCollapseStatement)
    (h₂ : ScaleViolationStatement) :
    ¬ (mixedIdentities ↥qTwo 1).IsFinitelyNormallyGenerated := by
  apply not_isFinitelyNormallyGenerated_of_separating (H := Equiv.Perm ℚ)
  intro S hS hSJ
  obtain ⟨u, v, hu, huv, hv, hcol⟩ := h₁ S hS hSJ
  obtain ⟨w, hw, P, hPper, hP, hPw⟩ := h₂ u v hu huv hv
  exact ⟨evalPerm P, hcol P hPper hP, w, hw, hPw⟩

/-- **BFFHZ Question 3.3, answered negatively**, from the two dynamical statements: `Q₂` is a
finitely presented simple group whose mixed identities are not finitely normally generated. -/
theorem mixedIdentities_statement_of (h₁ : SmallSupportCollapseStatement)
    (h₂ : ThreeArcViolationStatement) :
    ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧ IsSimpleGroup G ∧
      ∃ n : ℕ, ¬ (mixedIdentities G n).IsFinitelyNormallyGenerated :=
  ⟨↥qTwo, inferInstance, isFinitelyPresented_qTwo, isSimpleGroup_qTwo_closed, 1,
    not_isFinitelyNormallyGenerated_qTwo h₁ (scaleViolation_of_threeArc h₂)⟩

#audit_closed_axioms GroupApproximation.BHPalomar.MixedIdentities.isFinitelyPresented_qTwo
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.exists_qTwo_supportedIn
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.threeArcWord_mem_mixedIdentities
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.not_isFinitelyNormallyGenerated_qTwo
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.mixedIdentities_statement_of

end MixedIdentities
end BHPalomar
end GroupApproximation
