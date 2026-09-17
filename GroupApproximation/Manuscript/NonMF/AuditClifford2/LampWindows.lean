import GroupApproximation.Sofic.SoficMarkedCompression
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Sofic.CentralInvolutionFinite
import GroupApproximation.Sofic.SoficInvariantFiniteKernel
import GroupApproximation.Sofic.SoficTelescope
import Mathlib.GroupTheory.Commutator.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Finite lamp windows in the proof that the Clifford witness is locally RF

`non_mf_groups_exist.tex`, proof of `prop:clifford-locally-rf`, lines 2033--2041:

> A finite subset of $W_0$ involves only finitely many lamps $c_x$, and its
> $T_\alpha$-coordinates lie in one $\Gamma_n$.  Let $Y$ be the union of
> the $\Gamma_n$-orbits of these finitely many $x$.  Then $Y$ is finite
> and $\Gamma_n$-invariant, and the finite subset is contained in
> \[ C_Y\rtimes\Gamma_n, \]
> where $C_Y=\langle\varepsilon,c_y:y\in Y\rangle$ is finite by the
> normal form above.

Corpus dictionary: `W_0 = ShiftKernelFor α hα = C(X) ⋊ T_α`, `X = Cosets α hα`,
`Γ_n = (level α hα n).range`, and the action of `Γ_n` on sites is
`SoficMarkedCompression.levelSiteAction α hα n`.

Proof route.
* `lampWindow S = ⟨ε, c_x : x ∈ S⟩`. Every Clifford lamp element lies in some
  window over a finite set: this is closure induction on the generators
  (`CliffordLamp.mem_subgroup_of_sign_mem_of_lamp_mem`). The telescope
  coordinates of finitely many elements lie in one level
  (`exists_level_repr`, `level_mem_range_of_le`).
* `siteWindow α hα n S = Y` is the union of the `Γ_n`-orbits. It is finite by
  `finite_levelSiteAction_orbit` and invariant because the action is a
  homomorphism.
* `C_Y` is finite. The corpus route is not the normal form but the equivalent
  central-involution pattern `finite_closure_of_central_involution`: `ε` is a
  central involution, each lamp is an involution, and distinct lamps have
  commutator `ε`.
* `C_Y` is `Γ_n`-invariant (`level_action_eq_baseAction`). The finite subset
  lies in the image of `C_Y ⋊ Γ_n` under `inclSemidirect`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditClifford2

open MappingTelescope MarkedCompression CliffordLamp SoficMarkedCompression
  CliffordWitnessLocallyRFByInt SemidirectProduct
open scoped commutatorElement

noncomputable section

/-- The lamp window `⟨ε, c_x : x ∈ S⟩`. -/
abbrev lampWindow {X : Type*} (S : Set X) : Subgroup (CliffordLamp X) :=
  Subgroup.closure (insert (CliffordLamp.sign X) (CliffordLamp.lamp X '' S))

theorem lampWindow_mono {X : Type*} {S T : Set X} (h : S ⊆ T) :
    lampWindow S ≤ lampWindow T :=
  Subgroup.closure_mono (Set.insert_subset_insert (Set.image_mono h))

/-- Every Clifford lamp element involves only finitely many lamps. -/
theorem exists_finset_mem_lampWindow {X : Type*} (c : CliffordLamp X) :
    ∃ S : Finset X, c ∈ lampWindow (S : Set X) := by
  classical
  have hc : c ∈ Subgroup.closure
      (insert (CliffordLamp.sign X) (Set.range (CliffordLamp.lamp X))) :=
    CliffordLamp.mem_subgroup_of_sign_mem_of_lamp_mem X _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (fun x ↦ Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨x, rfl⟩)) c
  induction hc using Subgroup.closure_induction with
  | mem d hd =>
      rcases Set.mem_insert_iff.mp hd with rfl | ⟨x, rfl⟩
      · exact ⟨∅, Subgroup.subset_closure (Set.mem_insert _ _)⟩
      · exact ⟨{x}, Subgroup.subset_closure (Set.mem_insert_of_mem _
          ⟨x, Finset.mem_coe.mpr (Finset.mem_singleton_self x), rfl⟩)⟩
  | one => exact ⟨∅, Subgroup.one_mem _⟩
  | mul _ _ _ _ ha hb =>
      obtain ⟨S, hS⟩ := ha
      obtain ⟨T, hT⟩ := hb
      exact ⟨S ∪ T, Subgroup.mul_mem _
        (lampWindow_mono (Finset.coe_subset.mpr Finset.subset_union_left) hS)
        (lampWindow_mono (Finset.coe_subset.mpr Finset.subset_union_right) hT)⟩
  | inv _ _ ha =>
      obtain ⟨S, hS⟩ := ha
      exact ⟨S, Subgroup.inv_mem _ hS⟩

/-- A lamp window over a finite set of sites is finite. -/
theorem finite_lampWindow {X : Type*} {Y : Set X} (hY : Y.Finite) :
    Finite (lampWindow Y) := by
  refine finite_closure_of_central_involution (CliffordLamp.sign_sq X)
    (CliffordLamp.sign_commute X) (hY.image (CliffordLamp.lamp X)) ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact CliffordLamp.lamp_sq X x
  · rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    rw [← commutatorElement_def]
    by_cases hxy : x = y
    · subst hxy
      rw [commutatorElement_self]
      exact Subgroup.one_mem _
    · rw [CliffordLamp.commutator_lamp_lamp X hxy]
      exact Subgroup.mem_zpowers _

/-- An invariant set of sites gives an invariant lamp window. -/
theorem lampWindow_invariant {H X : Type*} [Group H] (ρ : H →* Equiv.Perm X)
    {Y : Set X} (hY : ∀ h : H, ∀ y ∈ Y, ρ h y ∈ Y) (h : H) {c : CliffordLamp X}
    (hc : c ∈ Subgroup.closure
      (insert (CliffordLamp.sign X) (CliffordLamp.lamp X '' Y))) :
    CliffordLamp.actionHom ρ h c ∈ Subgroup.closure
      (insert (CliffordLamp.sign X) (CliffordLamp.lamp X '' Y)) := by
  induction hc using Subgroup.closure_induction with
  | mem d hd =>
      apply Subgroup.subset_closure
      rcases Set.mem_insert_iff.mp hd with rfl | ⟨y, hy, rfl⟩
      · rw [CliffordLamp.actionHom_apply_sign]
        exact Set.mem_insert _ _
      · rw [CliffordLamp.actionHom_apply_lamp]
        exact Set.mem_insert_of_mem _ ⟨ρ h y, hY h y hy, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul _ _ _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv _ _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- tex 2033--2034: a finite subset of `W_0` involves only finitely many lamps
`c_x`, and its `T_α`-coordinates lie in one `Γ_n`. -/
theorem manuscriptSentence_finiteSubsetFiniteLampsOneLevel
    (F : Finset (ShiftKernelFor α hα)) :
    ∃ (S : Finset (Cosets α hα)) (n : ℕ), ∀ g ∈ F,
      g.left ∈ lampWindow (S : Set (Cosets α hα)) ∧
        g.right ∈ (level α hα n).range := by
  classical
  choose T hT using fun g : ShiftKernelFor α hα ↦ exists_finset_mem_lampWindow g.left
  choose lvl elt hrepr using fun g : ShiftKernelFor α hα ↦ exists_level_repr α hα g.right
  refine ⟨F.biUnion T, F.sup lvl, fun g hg ↦ ⟨?_, ?_⟩⟩
  · exact lampWindow_mono (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem T hg)) (hT g)
  · have hmem := level_mem_range_of_le α hα (Finset.le_sup (f := lvl) hg) (elt g)
    rwa [hrepr g] at hmem

#audit_axioms manuscriptSentence_finiteSubsetFiniteLampsOneLevel

/-- The union `Y` of the `Γ_n`-orbits of the sites in `S`. -/
abbrev siteWindow (n : ℕ) (S : Finset (Cosets α hα)) : Set (Cosets α hα) :=
  ⋃ x ∈ (S : Set (Cosets α hα)),
    Set.range fun τ : (level α hα n).range ↦ levelSiteAction α hα n τ x

/-- tex 2034--2035 (definition): `Y` is the union of the `Γ_n`-orbits of the
finitely many sites `x ∈ S`, where `Γ_n` acts on `X = V/Γ` through `T_α → V`. -/
theorem manuscriptSentence_orbitUnionDefinition (n : ℕ) (S : Finset (Cosets α hα)) :
    ∀ y : Cosets α hα, y ∈ siteWindow α hα n S ↔
      ∃ x ∈ S, ∃ τ : (level α hα n).range,
        (inl (τ : Telescope α hα) : Vertical α hα) • x = y := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, τ, hτ⟩ := Set.mem_iUnion₂.mp hy
    exact ⟨x, Finset.mem_coe.mp hx, τ, hτ⟩
  · rintro ⟨x, hx, τ, hτ⟩
    exact Set.mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hx, τ, hτ⟩

#audit_axioms manuscriptSentence_orbitUnionDefinition

theorem finite_siteWindow [α.range.FiniteIndex] (n : ℕ) (S : Finset (Cosets α hα)) :
    (siteWindow α hα n S).Finite :=
  Set.Finite.biUnion S.finite_toSet fun x _ ↦ finite_levelSiteAction_orbit α hα n x

theorem siteWindow_invariant (n : ℕ) (S : Finset (Cosets α hα)) :
    ∀ τ : (level α hα n).range, ∀ y ∈ siteWindow α hα n S,
      levelSiteAction α hα n τ y ∈ siteWindow α hα n S := by
  intro τ y hy
  obtain ⟨x, hx, σ, rfl⟩ := Set.mem_iUnion₂.mp hy
  refine Set.mem_iUnion₂.mpr ⟨x, hx, τ * σ, ?_⟩
  show levelSiteAction α hα n (τ * σ) x =
    levelSiteAction α hα n τ (levelSiteAction α hα n σ x)
  rw [map_mul, Equiv.Perm.mul_apply]

theorem subset_siteWindow (n : ℕ) (S : Finset (Cosets α hα)) :
    (S : Set (Cosets α hα)) ⊆ siteWindow α hα n S := by
  intro x hx
  refine Set.mem_iUnion₂.mpr ⟨x, hx, 1, ?_⟩
  show levelSiteAction α hα n 1 x = x
  rw [map_one, Equiv.Perm.one_apply]

/-- The finite lamp subgroup `C_Y`. -/
abbrev cliffordWindow (n : ℕ) (S : Finset (Cosets α hα)) :
    Subgroup (CliffordLamp (Cosets α hα)) :=
  lampWindow (siteWindow α hα n S)

theorem cliffordWindow_invariant (n : ℕ) (S : Finset (Cosets α hα)) :
    ∀ h ∈ (level α hα n).range, ∀ c ∈ cliffordWindow α hα n S,
      SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα) h c ∈
        cliffordWindow α hα n S := by
  intro h hh c hc
  have hact := lampWindow_invariant (levelSiteAction α hα n)
    (siteWindow_invariant α hα n S) ⟨h, hh⟩ hc
  rw [level_action_eq_baseAction] at hact
  exact hact

/-- tex 2035--2039: `Y` is finite and `Γ_n`-invariant, and the finite subset
lies in `C_Y ⋊ Γ_n`, embedded in `W_0` by `inclSemidirect`. -/
theorem manuscriptSentence_orbitUnionFiniteInvariantContains [α.range.FiniteIndex]
    (F : Finset (ShiftKernelFor α hα)) :
    ∃ (S : Finset (Cosets α hα)) (n : ℕ), (siteWindow α hα n S).Finite ∧
      (∀ τ : (level α hα n).range, ∀ y ∈ siteWindow α hα n S,
        levelSiteAction α hα n τ y ∈ siteWindow α hα n S) ∧
      ∀ g ∈ F, g ∈ (inclSemidirect
        (SemidirectAssoc.baseAction (shiftHom α hα) (lampAction α hα))
        (cliffordWindow α hα n S) (level α hα n).range
        (cliffordWindow_invariant α hα n S)).range := by
  obtain ⟨S, n, hF⟩ := manuscriptSentence_finiteSubsetFiniteLampsOneLevel α hα F
  refine ⟨S, n, finite_siteWindow α hα n S, siteWindow_invariant α hα n S,
    fun g hg ↦ ?_⟩
  obtain ⟨hleft, hright⟩ := hF g hg
  exact ⟨⟨⟨g.left, lampWindow_mono (subset_siteWindow α hα n S) hleft⟩,
    ⟨g.right, hright⟩⟩, by rw [inclSemidirect_apply]⟩

#audit_axioms manuscriptSentence_orbitUnionFiniteInvariantContains

/-- tex 2040--2041: `C_Y = ⟨ε, c_y : y ∈ Y⟩` is finite. -/
theorem manuscriptSentence_cliffordWindowFinite [α.range.FiniteIndex] (n : ℕ)
    (S : Finset (Cosets α hα)) :
    cliffordWindow α hα n S = Subgroup.closure
        (insert (CliffordLamp.sign (Cosets α hα))
          (CliffordLamp.lamp (Cosets α hα) '' siteWindow α hα n S)) ∧
      Finite (cliffordWindow α hα n S) :=
  ⟨rfl, finite_lampWindow (finite_siteWindow α hα n S)⟩

#audit_axioms manuscriptSentence_cliffordWindowFinite

end

end GroupApproximation.Manuscript.NonMF.AuditClifford2
