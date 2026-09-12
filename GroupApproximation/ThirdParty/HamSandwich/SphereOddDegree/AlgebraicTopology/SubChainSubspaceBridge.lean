import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.MayerVietoris
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.BallBoundaryLES

/-!
# Bridge: subordinate-chain complex ≅ singular chains of the subspace

For a topological space `X` and a subset `S ⊆ X`, the subordinate-chain complex
`subChainComplex R X S` (singular chains of `X` supported in `S`) is isomorphic,
as a chain complex, to the singular chain complex of the *subspace* `S`.  The
isomorphism is induced by the inclusion `S ↪ X`: on a basis simplex `τ` of the
subspace it sends `[τ]` to `[ι ∘ τ]`, which has image in `S`, hence is
subordinate.

This is the geometric "bridge" needed to feed contractibility (and homotopy
equivalence) of subspaces into the Mayer–Vietoris vanishing hypotheses.

## Main results

* `subspaceHomologyIso` — the chain-level homology isomorphism in every degree.
* `subspaceHomologyIsoℤ` — its integral specialization, identifying the
  subordinate-chain homology with `Hₙ` of the subspace.
* `isZero_subChainComplex_homology_of_contractible` — for a contractible subspace
  `S` and `n ≥ 1`, the subordinate-chain homology vanishes.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision

variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The inclusion of a subspace `S ⊆ X` as a morphism of topological spaces. -/
def sInclusion (S : Set X) : TopCat.of S ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem sInclusion_hom_apply (S : Set X) (x : S) :
    (ConcreteCategory.hom (sInclusion S)) x = (x : X) := rfl

/-
Pushing a simplex of the subspace forward along the inclusion lands a simplex
subordinate to `S`.
-/
theorem isSubordinate_pushSimplex_sInclusion (S : Set X) (n : ℕ)
    (τ : singularSimplices (TopCat.of S) n) :
    IsSubordinate S (pushSimplex (sInclusion S) n τ) := by
      -- Unfold `IsSubordinate` and `singularSimplexAsContinuousMap` to reduce the goal to showing the range of
      -- `singularSimplexAsContinuousMap X n (pushSimplex (sInclusion S) n τ)` is contained in `S`.
      simp [IsSubordinate, singularSimplexAsContinuousMap,
        pushSimplex_continuousMap (sInclusion S) n τ];
      exact Set.range_subset_iff.mpr fun x => by simp +decide [ sInclusion ] ;

/-
The pushforward of simplices along the inclusion is injective.
-/
theorem pushSimplex_sInclusion_injective (S : Set X) (n : ℕ) :
    Function.Injective (pushSimplex (sInclusion S) n) := by
      intro τ₁ τ₂ h_eq;
      apply_fun fun x => singularSimplexAsContinuousMap X n x at h_eq;
      rw [ pushSimplex_continuousMap, pushSimplex_continuousMap ] at h_eq;
      simp_all +decide [ sInclusion ];
      convert h_eq using 1;
      simp +decide [ singularSimplexAsContinuousMap ]

/-
Every simplex of `X` subordinate to `S` is the pushforward of a (unique)
simplex of the subspace `S`.
-/
theorem exists_pushSimplex_of_subordinate (S : Set X) (n : ℕ)
    {σ : singularSimplices X n} (hσ : IsSubordinate S σ) :
    ∃ τ, pushSimplex (sInclusion S) n τ = σ := by
      -- By definition of `IsSubordinate`, we know that the range of `mvSimplexMap σ` is contained in `S`.
      have h_range : Set.range (singularSimplexAsContinuousMap X n σ) ⊆ S := hσ
      obtain ⟨g, hg⟩ : ∃ g : C(Delta n, S), (ConcreteCategory.hom (sInclusion S)).comp g = singularSimplexAsContinuousMap X n σ := by
        exact ⟨ ContinuousMap.mk fun x => ⟨ singularSimplexAsContinuousMap X n σ x, h_range <| Set.mem_range_self x ⟩, by ext; rfl ⟩;
      use continuousMapAsSingularSimplex (TopCat.of S) n g;
      apply_fun singularSimplexAsContinuousMap X n at *;
      convert hg using 1;
      rw [pushSimplex_continuousMap]
      simp only [singularSimplexAsContinuousMap, continuousMapAsSingularSimplex,
        Equiv.apply_symm_apply]

/-
The chain map induced by the inclusion sends any chain of the subspace into
the subordinate-chain submodule.
-/
theorem singularChainMap_sInclusion_mem (S : Set X) (n : ℕ)
    (c : singularChainGroup R (TopCat.of S) n) :
    (singularChainMap R (sInclusion S) n).hom c ∈ subChainSubmodule R X S n := by
      obtain ⟨μ, hμ⟩ : ∃ (μ : Finset (singularSimplices (TopCat.of S) n)) (c' : singularSimplices (TopCat.of S) n →₀ R),
          c = μ.sum (fun (σ : singularSimplices (TopCat.of S) n) => c' σ • chainGenerator R { carrier := S, str := instTopologicalSpaceSubtype } n σ) := by
                                                                                                obtain ⟨μ, c', hc⟩ : ∃ (μ : Finset (singularSimplices (TopCat.of S) n)) (c' : singularSimplices (TopCat.of S) n →₀ R),
                                                                                                      c = μ.sum (fun (σ : singularSimplices (TopCat.of S) n) => c' σ • chainGenerator R { carrier := S, str := instTopologicalSpaceSubtype } n σ) := by
                                                                                                  have h_span : Submodule.span R (Set.range (fun σ : singularSimplices (TopCat.of S) n => chainGenerator R { carrier := S, str := instTopologicalSpaceSubtype } n σ)) = ⊤ := by
                                                                                                                                                                                                              grind +suggestions
                                                                                                  have := h_span.ge ( Submodule.mem_top : c ∈ ⊤ );
                                                                                                  rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at this;
                                                                                                  obtain ⟨ c', hc' ⟩ := this; use c'.support, c'; simp_all +decide [ Finsupp.sum ] ;
                                                                                                use μ, c';
      obtain ⟨ c', rfl ⟩ := hμ;
      simp +decide [ subChainSubmodule, singularChainMap_generator ];
      exact Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ <| Submodule.subset_span ⟨ _, isSubordinate_pushSimplex_sInclusion S n x, rfl ⟩

/-
The inclusion-induced chain map, corestricted to the subordinate-chain
complex of `S`.
-/
def subChainCorestrict (R : Type) [CommRing R] (X : TopCat.{0}) (S : Set X) :
    ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).obj (TopCat.of S) ⟶
      subChainComplex R X S where
  f n := ModuleCat.ofHom
    (LinearMap.codRestrict (subChainSubmodule R X S n)
      (singularChainMap R (sInclusion S) n).hom (singularChainMap_sInclusion_mem S n))
  comm' i j hij := by
    obtain ⟨ k, hk ⟩ := hij;
    ext c;
    have := singularChainMap_boundary_apply R ( sInclusion S ) j ( c : singularChainGroup R ( TopCat.of S ) ( j + 1 ) ) ; simp_all +decide [ singularBoundary ] ;
    exact Subtype.ext this

/-- A reindexing of simplices `g` induces, via the coproduct universal property, a
linear map on chain groups; it sends a basis generator `[σ]` to `[g σ]`. -/
noncomputable def reindexChainMap (R : Type) [CommRing R] {Y : TopCat.{0}} (n : ℕ)
    (g : singularSimplices Y n → singularSimplices X n) :
    singularChainGroup R Y n ⟶ singularChainGroup R X n :=
  Limits.Sigma.desc (fun s => Limits.Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R) (g s))

@[simp] theorem reindexChainMap_generator {Y : TopCat.{0}} (n : ℕ)
    (g : singularSimplices Y n → singularSimplices X n) (σ : singularSimplices Y n) :
    (reindexChainMap R n g).hom (chainGenerator R Y n σ) = chainGenerator R X n (g σ) := by
  have h :
      Limits.Sigma.ι (fun _ : singularSimplices Y n => ModuleCat.of R R) σ ≫
          Limits.Sigma.desc (fun s =>
            Limits.Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R) (g s)) =
        Limits.Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R) (g σ) :=
    Limits.Sigma.ι_desc _ _
  have h1 := congrArg
    (fun f : ModuleCat.of R R ⟶ singularChainGroup R X n => f.hom (1 : R)) h
  change
    (ModuleCat.Hom.hom
      (Limits.Sigma.ι (fun _ : singularSimplices Y n => ModuleCat.of R R) σ ≫
        Limits.Sigma.desc (fun s =>
          Limits.Sigma.ι (fun _ : singularSimplices X n => ModuleCat.of R R) (g s)))) 1 = _
  exact h1

/-
If `g` is a set-level left inverse of `pushSimplex f n`, then `reindexChainMap R n g`
is a left inverse of `singularChainMap R f n` at the level of chain groups.
-/
theorem reindexChainMap_comp_singularChainMap {Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (g : singularSimplices Y n → singularSimplices X n)
    (hg : Function.LeftInverse g (pushSimplex f n)) :
    singularChainMap R f n ≫ reindexChainMap R n g = 𝟙 _ := by
      ext τ
      simp;
      obtain ⟨μ, c', hc⟩ : ∃ (μ : Finset (singularSimplices X n)) (c' : singularSimplices X n →₀ R),
          τ = μ.sum (fun (σ : singularSimplices X n) => c' σ • chainGenerator R X n σ) := by
            have h_span : Submodule.span R (Set.range (fun σ : singularSimplices X n => chainGenerator R X n σ)) = ⊤ := by
              grind +suggestions;
            have := h_span.ge ( Submodule.mem_top : τ ∈ ⊤ );
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at this; obtain ⟨ c', hc' ⟩ := this; use c'.support, c'; simp_all +decide [ Finsupp.sum ] ;
      simp +decide [ hc, singularChainMap_generator, reindexChainMap_generator ];
      exact Finset.sum_congr rfl fun x hx => by rw [ hg x ] ;

/-
The free-module chain map induced by an injective reindexing of simplices is
injective.  A left inverse is built from any set-level retraction of the index
map.
-/
theorem singularChainMap_injective_of_pushSimplex_injective {Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (hf : Function.Injective (pushSimplex f n)) :
    Function.Injective (singularChainMap R f n).hom := by
      by_cases h : Nonempty (singularSimplices X n);
      · have := @reindexChainMap_comp_singularChainMap R _ X Y f n ( Function.invFun ( pushSimplex f n ) ) ( Function.leftInverse_invFun hf );
        exact Function.HasLeftInverse.injective ⟨ _, fun x => by simpa using congr_arg ( fun g => g x ) this ⟩;
      · intro x y; simp_all +decide [ singularChainMap ] ;
        -- Since the index type is empty, the coproduct is initial, hence zero.
        have h_zero : Subsingleton (singularChainGroup R X n) := by
          have h_empty : ∀ (x : singularChainGroup R X n), x = 0 := by
            intro x; exact (by
            obtain ⟨ μ, c', hc ⟩ := ( show ∃ μ : Finset ( singularSimplices X n ), ∃ c' : singularSimplices X n →₀ R, x = μ.sum ( fun σ => c' σ • chainGenerator R X n σ ) from by
                                        have h_span : Submodule.span R (Set.range (fun σ : singularSimplices X n => chainGenerator R X n σ)) = ⊤ := by
                                          grind +suggestions;
                                        have := h_span.ge ( Submodule.mem_top : x ∈ ⊤ ) ; rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at this; obtain ⟨ c', hc' ⟩ := this; use c'.support, c'; simp_all +decide [ Finsupp.sum ] ; );
            exact hc.trans ( Finset.sum_eq_zero fun σ hσ => False.elim <| h.elim σ ))
          exact ⟨fun x y => h_empty x ▸ h_empty y ▸ rfl⟩;
        exact fun _ => Subsingleton.elim _ _

/-
Each degree of the corestricted chain map is bijective.
-/
theorem subChainCorestrict_bijective (S : Set X) (n : ℕ) :
    Function.Bijective ((subChainCorestrict R X S).f n).hom := by
      constructor;
      · intro x y hxy;
        apply singularChainMap_injective_of_pushSimplex_injective
          (f := sInclusion S) n (pushSimplex_sInclusion_injective S n);
        have hv := congrArg Subtype.val hxy;
        change (singularChainMap R (sInclusion S) n).hom x =
          (singularChainMap R (sInclusion S) n).hom y at hv;
        exact hv;
      · intro x;
        rcases x with ⟨ x, hx ⟩;
        induction hx using Submodule.span_induction;
        · obtain ⟨ σ, hσ, rfl ⟩ := ‹_›;
          obtain ⟨ τ, hτ ⟩ := exists_pushSimplex_of_subordinate S n hσ;
          use chainGenerator R (TopCat.of S) n τ;
          apply Subtype.ext;
          change (singularChainMap R (sInclusion S) n).hom
              (chainGenerator R (TopCat.of S) n τ) = _;
          simpa only [hτ] using singularChainMap_generator R (sInclusion S) n τ;
        · refine ⟨0, ?_⟩;
          apply Subtype.ext;
          exact map_zero _;
        · rename_i hx hy;
          refine ⟨hx.choose + hy.choose, ?_⟩;
          calc
            ((subChainCorestrict R X S).f n).hom (hx.choose + hy.choose) =
                ((subChainCorestrict R X S).f n).hom hx.choose +
                  ((subChainCorestrict R X S).f n).hom hy.choose := map_add _ _ _
            _ = _ := congrArg₂ (· + ·) hx.choose_spec hy.choose_spec;
        · obtain ⟨pre, hpre⟩ := ‹∃ pre, _›;
          refine ⟨(‹R›) • pre, ?_⟩;
          calc
            ((subChainCorestrict R X S).f n).hom ((‹R›) • pre) =
                (‹R›) • ((subChainCorestrict R X S).f n).hom pre := map_smul _ _ _
            _ = _ := congrArg ((‹R›) • ·) hpre;

instance subChainCorestrict_component_isIso (S : Set X) (n : ℕ) :
    IsIso ((subChainCorestrict R X S).f n) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (subChainCorestrict_bijective S n)

instance subChainCorestrict_isIso (S : Set X) :
    IsIso (subChainCorestrict R X S) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **The bridge on homology.** The subordinate-chain homology of `S ⊆ X` is
isomorphic to the singular homology of the subspace `S`. -/
def subspaceHomologyIso (S : Set X) (n : ℕ) :
    (subChainComplex R X S).homology n ≅
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).obj (TopCat.of S)).homology n :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso (asIso (subChainCorestrict R X S))).symm

/-- **Integral bridge on homology.** The subordinate-chain homology of `S ⊆ X` is
isomorphic to `Hₙ(S; ℤ)`, the integral singular homology of the subspace. -/
def subspaceHomologyIsoℤ (X : TopCat.{0}) (S : Set X) (n : ℕ) :
    (subChainComplex ℤ X S).homology n ≅ (singularHomologyℤ n).obj (TopCat.of S) :=
  subspaceHomologyIso S n

/-- **Vanishing for contractible subspaces.** If `S ⊆ X` is contractible and
`n ≥ 1`, then the subordinate-chain homology vanishes. -/
theorem isZero_subChainComplex_homology_of_contractible
    (X : TopCat.{0}) (S : Set X) [ContractibleSpace S] (n : ℕ) (hn : 1 ≤ n) :
    IsZero ((subChainComplex ℤ X S).homology n) :=
  IsZero.of_iso (isZero_singularHomologyℤ_of_contractibleSpace n hn S)
    (subspaceHomologyIsoℤ X S n)

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
