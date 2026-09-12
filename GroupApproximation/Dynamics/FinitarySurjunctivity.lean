import GroupApproximation.Dynamics.FinitaryTransplant
import GroupApproximation.Dynamics.StratifiedPeeling
import GroupApproximation.Dynamics.SurjunctivitySubgroup
import GroupApproximation.Dynamics.SurjunctivityTransfer

/-!
# Finitary split extensions preserve surjunctivity

The common finite-fiber transplants satisfy the proved Boolean-strata
peeling theorem. Their surjectivity, together with finite-set separation,
proves surjunctivity of the semidirect product.
-/

namespace GroupApproximation.Surjunctivity

universe uN uG uX uA uQ uB

variable {N : Type uN} {G : Type uG} {X : Type uX}
  [Group N] [Group G] [MulAction G X]
  {α : G →* MulAut N} {A : Finset X → Type uA} [∀ S, Group (A S)]
  {Q : Type uQ} [Group Q] {B : Type uB}

/-- Uniform finite dependence and equivariance give an exact finite local rule. -/
theorem exists_localMap_of_continuous_equivariant
    [TopologicalSpace B] [CompactSpace B] [DiscreteTopology B]
    {τ : (G → B) → (G → B)} (hcont : Continuous τ) (heq : IsEquivariant τ) :
    ∃ (M : Finset G) (μ : (M → B) → B), τ = localMap M μ := by
  classical
  obtain ⟨M, hM⟩ := isFiniteMemory_of_continuous_equivariant hcont heq
  let F := insert 1 M
  let μ : (F → B) → B := fun v ↦
    τ (fun h ↦ if hh : h ∈ F then v ⟨h, hh⟩ else v ⟨1, Finset.mem_insert_self _ _⟩) 1
  refine ⟨F, μ, ?_⟩
  funext x g
  change τ x g =
    τ (fun h ↦ if hh : h ∈ F then x (g * (⟨h, hh⟩ : F))
      else x (g * (⟨1, Finset.mem_insert_self _ _⟩ : F))) 1
  calc
    τ x g = τ (shift g x) 1 := by
      simpa only [shift, mul_one] using (congrFun (heq g x) 1).symm
    _ = _ := by
      apply hM
      intro m hm
      simp [shift, F, hm]

namespace FinitarySite

variable (D : FinitarySite α A)

include D

/-- Boolean-strata peeling makes every finite-fiber transplant surjective. -/
theorem quotientLocalMap_surjective [Finite Q] [Fintype B]
    [TopologicalSpace B] [DiscreteTopology B] (hG : IsSurjunctive G)
    (S : Finset X) (q : A S →* Q)
    (M : Finset (SemidirectProduct N G α)) (μ : (M → B) → B)
    (hτ : Function.Injective (localMap M μ)) :
    Function.Surjective (D.quotientLocalMap S q M μ) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  let Z : S → Set G := fun s ↦ siteStratum (D.memorySites M) (s : X)
  let K : Finset S → Subgroup G := fun U ↦ siteStabilizer (boundedSites S U)
  have hK (U : Finset S) : IsSurjunctive (K U) := hG.subgroup (K U)
  have hanti (V U : Finset S) (hVU : V ⊆ U) : K U ≤ K V :=
    siteStabilizer_antitone (boundedSites_mono S hVU)
  have hinj (U : Finset S) : Function.Injective (D.boundedWindow S q M μ U).toFun :=
    D.quotientCurried_injective _ _ M μ hτ
  have hequiv (U : Finset S) (k : K U) (x : G → Q → B) (g : G) :
      (D.boundedWindow S q M μ U).toFun (shift (k : G) x) g =
        (D.boundedWindow S q M μ U).toFun x ((k : G) * g) :=
    D.quotientCurried_stabilizer _ _ M μ k x g
  have hslice (U V : Finset S) (hVU : V ⊆ U) (x : G → Q → B) (g : G)
      (haway : ∀ s ∈ U, s ∉ V → g ∉ Z s) :
      (D.boundedWindow S q M μ U).toFun x g =
        (D.boundedWindow S q M μ V).toFun x g :=
    D.boundedWindow_compatible S q M μ hVU x g haway
  have hcover (U : Finset S) (F : Finset G) :
      ∃ T : Finset G, ∀ g ∈ stratumRegion Z U F, ∃ r ∈ T, g * r⁻¹ ∈ K U := by
    obtain ⟨T, hT⟩ := finite_coset_cover_strataRegion (G := G)
      (boundedSites S U) (D.memorySites M) F
    refine ⟨T, ?_⟩
    intro g hg
    apply hT g
    intro s hs
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hs
    exact hg u hu
  have hbij := stratified_bijective (canonicalSubsetSchedule S) Z
    (D.boundedWindow S q M μ) K hK hanti hinj hequiv hslice hcover Finset.univ
  apply D.quotientLocalMap_surjective_of_curried S q M μ
  have heq : (D.boundedWindow S q M μ Finset.univ).toFun =
      D.quotientCurried S q M μ := by
    funext y g u
    apply congrArg μ
    funext m
    have hc := D.coefficient_of_support S (boundedSites S Finset.univ)
      (boundedSites_subset S Finset.univ) q g m.val.left (by
        intro x _ hx
        rwa [boundedSites_univ])
    exact congrArg (y (g * m.val.right)) (congrArg (u * ·) hc.symm)
  rw [heq] at hbij
  exact hbij.surjective

/-- Surjectivity of injective local maps on the finitary split extension. -/
theorem localMap_surjective [Fintype B] [TopologicalSpace B] [DiscreteTopology B]
    (hG : IsSurjunctive G) (M : Finset (SemidirectProduct N G α))
    (μ : (M → B) → B) (hτ : Function.Injective (localMap M μ)) :
    Function.Surjective (localMap M μ) := by
  classical
  let I := Σ S : Finset X, {K : Subgroup (A S) // K.Normal ∧ K.FiniteIndex}
  letI (i : I) : i.2.1.Normal := i.2.2.1
  letI (i : I) : i.2.1.FiniteIndex := i.2.2.2
  let Ω : I → Type (max uA uG) := fun i ↦ (A i.1 ⧸ i.2.1) × G
  let π (i : I) : SemidirectProduct N G α → Ω i :=
    D.quotientCoordinate i.1 (QuotientGroup.mk' i.2.1)
  have hπ (i : I) : Function.Surjective (π i) :=
    D.quotientCoordinate_surjective i.1 _ (QuotientGroup.mk'_surjective i.2.1)
  let τΩ (i : I) : (Ω i → B) → (Ω i → B) :=
    D.quotientLocalMap i.1 (QuotientGroup.mk' i.2.1) M μ
  apply transplant_surjective_finite π hπ (localMap M μ) τΩ (continuous_localMap M μ)
  · exact fun i ↦ D.quotientLocalMap_intertwining i.1 _ M μ
  · intro F
    obtain ⟨S, K, hKn, hKf, hF⟩ := D.exists_quotientCoordinate_injOn F
    exact ⟨⟨S, ⟨K, hKn, hKf⟩⟩, hF⟩
  · intro i
    exact D.quotientLocalMap_surjective hG i.1 _ M μ hτ

/-- A finitary split extension of a surjunctive group is surjunctive. -/
theorem isSurjunctive (hG : IsSurjunctive G) :
    IsSurjunctive (SemidirectProduct N G α) := by
  intro B _ _ _ τ hcont heq hinj
  obtain ⟨M, μ, rfl⟩ := exists_localMap_of_continuous_equivariant hcont heq
  exact D.localMap_surjective hG M μ hinj

/-- A finitary split extension is surjunctive exactly when its base is. -/
theorem isSurjunctive_iff : IsSurjunctive (SemidirectProduct N G α) ↔ IsSurjunctive G := by
  constructor
  · intro h
    exact h.of_injective (SemidirectProduct.inr : G →* SemidirectProduct N G α)
      SemidirectProduct.inr_injective
  · exact D.isSurjunctive

end FinitarySite

end GroupApproximation.Surjunctivity
