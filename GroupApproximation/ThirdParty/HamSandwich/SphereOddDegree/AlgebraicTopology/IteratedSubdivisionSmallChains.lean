import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex
import Mathlib

/-!
# Finite chains eventually become small after iterated subdivision

Extending Prompt 16 from a single generator `[σ]` to an arbitrary singular
chain `c`, we prove: for every open cover `𝒰` of `X` and every chain `c`, some
iterated barycentric subdivision `sdᴺ(c)` lies in the small-chain submodule.

The argument uses that singular chains are *finite* `R`-linear combinations of
basis generators `[σ]` (the chain group is the free `R`-module on singular
simplices), so it suffices to handle each generator (Prompt 16) and combine via:

* `barycentricSubdivision_maps_smallChainSubmodule` — one subdivision keeps a
  small chain small (each affine summand has image inside the original image);
* `barycentricSubdivisionIter_maps_smallChainSubmodule` — hence every iterate
  does;
* `sdIter_mem_smallChainSubmodule_mono` — monotonicity in the number of
  subdivisions (taking a maximum over a finite support);
* `chainGenerator_span_top` — the generators span the chain group.

## Main result

* `exists_iteratedSubdivision_chain_mem_smallChains` — for every chain `c` there
  is `N` with `sdᴺ(c)` in the small-chain submodule.  This is the input to the
  later homology-surjectivity argument.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Limits

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

variable {X : TopCat.{0}}

/-! ## 1. Subdivision preserves smallness -/

/-
The underlying continuous map of one barycentric subdivision summand is
`σ ∘ a_π`.
-/
@[simp] theorem mvSimplexMap_barycentricSubdivSimplex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (σ : singularSimplices X n) :
    mvSimplexMap (barycentricSubdivSimplex X n π σ)
      = (mvSimplexMap σ).comp (affineSubdivContinuousMap n π) := by
  grind +suggestions

/-
Each barycentric subdivision summand of a small simplex is small.
-/
theorem IsSmallSimplex.barycentricSubdivSimplex {𝒰 : OpenCoverData X} {n : ℕ}
    {σ : singularSimplices X n} (hσ : IsSmallSimplex 𝒰 σ) (π : Equiv.Perm (Fin (n + 1))) :
    IsSmallSimplex 𝒰 (barycentricSubdivSimplex X n π σ) := by
  exact hσ.comp_of_range_subset _ ( mvSimplexMap_barycentricSubdivSimplex n π σ )

/-
**One subdivision preserves small chains.** The degree-wise barycentric
subdivision maps the small-chain submodule into itself.
-/
theorem barycentricSubdivision_maps_smallChainSubmodule (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      (barycentricSubdivisionLinearMap R X n).hom c ∈ smallChainSubmodule R X 𝒰 n := by
  intro c hc
  have hle : smallChainSubmodule R X 𝒰 n ≤ Submodule.comap (barycentricSubdivisionLinearMap R X n).hom (smallChainSubmodule R X 𝒰 n) := by
    refine' Submodule.span_le.mpr _;
    rintro c ⟨σ, hσ, rfl⟩
    simp [barycentricSubdivisionLinearMap_generator_sum, IsSmallSimplex.barycentricSubdivSimplex hσ];
    exact Submodule.sum_mem _ fun π _ => Submodule.smul_mem _ _ ( chainGenerator_mem_smallChainSubmodule ( IsSmallSimplex.barycentricSubdivSimplex hσ π ) )
  exact hle hc

/-
**Every iterate preserves small chains.**
-/
theorem barycentricSubdivisionIter_maps_smallChainSubmodule (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) (N n : ℕ) :
    ∀ c ∈ smallChainSubmodule R X 𝒰 n,
      barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n := by
  induction' N with N ih;
  · simp +decide [ barycentricSubdivisionIterLinearMap_zero ];
  · intro c hc; rw [ barycentricSubdivisionIterLinearMap_succ' ] ; exact barycentricSubdivision_maps_smallChainSubmodule R 𝒰 n _ ( ih _ hc ) ;

/-! ## 2. Iterate arithmetic and monotonicity -/

/-
`sd^(a+b) = sd^a ∘ sd^b` degree-wise.
-/
theorem barycentricSubdivisionIterLinearMap_add (R : Type) [CommRing R] (a b n : ℕ)
    (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (a + b) n c
      = barycentricSubdivisionIterLinearMap R X a n
          (barycentricSubdivisionIterLinearMap R X b n c) := by
  induction' a with a ih generalizing c;
  · simp +decide [ barycentricSubdivisionIterLinearMap_zero ];
  · grind +suggestions

/-
**Monotonicity in the number of subdivisions.** If `sd^N c` is a small chain
and `N ≤ M`, then `sd^M c` is a small chain.
-/
theorem sdIter_mem_smallChainSubmodule_mono (R : Type) [CommRing R]
    (𝒰 : OpenCoverData X) {N M n : ℕ} (hNM : N ≤ M) {c : singularChainGroup R X n}
    (hc : barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n) :
    barycentricSubdivisionIterLinearMap R X M n c ∈ smallChainSubmodule R X 𝒰 n := by
  convert barycentricSubdivisionIter_maps_smallChainSubmodule R 𝒰 ( M - N ) n _ hc using 1;
  rw [ ← barycentricSubdivisionIterLinearMap_add, Nat.sub_add_cancel hNM ]

/-! ## 3. Generators span the chain group -/

/-
The basis generators `[σ]` span the singular chain group (it is the free
`R`-module on singular simplices).
-/
theorem chainGenerator_span_top (R : Type) [CommRing R] (n : ℕ) :
    Submodule.span R (Set.range (chainGenerator R X n)) = ⊤ := by
  refine' Submodule.eq_top_iff'.mpr fun x => _;
  obtain ⟨c, hc⟩ : ∃ c : singularChainGroup R X n, x = c := by
    use x;
  -- Apply the `Limits.Sigma.hom_ext` lemma to conclude that `q = 0`.
  have hq_zero : (ModuleCat.ofHom (Submodule.mkQ (Submodule.span R (Set.range (chainGenerator R X n)))) : singularChainGroup R X n ⟶ ModuleCat.of R (singularChainGroup R X n ⧸ Submodule.span R (Set.range (chainGenerator R X n)))) = 0 := by
    apply Limits.colimit.hom_ext;
    intro j; ext; simp [chainGenerator];
    convert Submodule.Quotient.mk_eq_zero _ |>.2 <| Submodule.subset_span <| Set.mem_range_self j.as;
  convert Submodule.Quotient.mk_eq_zero _ |>.1 _;
  convert congr_arg ( fun f : singularChainGroup R X n ⟶ _ => f.hom c ) hq_zero using 1;
  exact hc ▸ rfl

/-! ## 4. Main theorem -/

/-
**Main deliverable.** For every singular chain `c` and every open cover `𝒰`,
some iterated barycentric subdivision `sdᴺ(c)` lies in the submodule of
`𝒰`-small chains.
-/
theorem exists_iteratedSubdivision_chain_mem_smallChains
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ) (c : singularChainGroup R X n) :
    ∃ N : ℕ,
      barycentricSubdivisionIterLinearMap R X N n c ∈ smallChainSubmodule R X 𝒰 n := by
  have h_chain_span : Submodule.span R (Set.range (chainGenerator R X n)) = ⊤ :=
    chainGenerator_span_top R n
  refine' Submodule.span_induction _ _ _ _ ( show c ∈ Submodule.span R ( Set.range ( chainGenerator R X n ) ) from h_chain_span.symm ▸ Submodule.mem_top );
  · rintro _ ⟨ σ, rfl ⟩ ; exact exists_iteratedSubdivision_generator_mem_smallChains 𝒰 R n σ;
  · exact ⟨ 0, by simp +decide [ barycentricSubdivisionIterLinearMap_zero ] ⟩;
  · rintro x y hx hy ⟨ Nx, hNx ⟩ ⟨ Ny, hNy ⟩;
    refine' ⟨ Max.max Nx Ny, _ ⟩;
    simp_all only [map_add];
    exact Submodule.add_mem _ ( sdIter_mem_smallChainSubmodule_mono R 𝒰 ( le_max_left _ _ ) hNx ) ( sdIter_mem_smallChainSubmodule_mono R 𝒰 ( le_max_right _ _ ) hNy );
  · intro a x hx hx'; obtain ⟨ N, hN ⟩ := hx'; use N; simp_all +decide [ Submodule.smul_mem ] ;

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
