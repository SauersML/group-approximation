import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SmallChains
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionDiameter
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionIter
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularSimplexLebesgueNumber
import Mathlib

/-!
# Each singular simplex eventually becomes small after iterated subdivision

For a singular simplex `σ : Δⁿ → X` and an open cover `𝒰` of `X`, some iterated
barycentric subdivision `sdᴺ([σ])` of the generator chain is a linear
combination of `𝒰`-small singular simplices.

The argument combines:

* the **Lebesgue number** of `σ` against `𝒰`
  (`singularSimplex_hasLebesgueNumber_for_openCover`, Prompt 15);
* the **diameter shrinking** of iterated barycentric subdivision
  (`exists_iteratedSubdivision_affine_diameter_lt`, Prompt 14);
* the **generator expansion** of the subdivision chain map (Prompts 01–05).

## Strategy

Every singular simplex appearing in `sdᴺ([σ])` has the form `σ ∘ a` where
`a : Δⁿ → Δⁿ` is an `N`-fold *affine* subdivision composite
(`affineCompMap`).  Working through the genuine linear map underlying the affine
subdivision (`affineSubdivLinear`), we identify the vertices of this composite
with Prompt 14's `iterVertices`, so its range has diameter
`< ε` for `N` large.  The Lebesgue number then forces `σ ∘ a` to be `𝒰`-small,
and the whole chain to lie in the small-chain submodule.

## Main results

* `support_iteratedSubdivision_generator_subset_affineSummands` — `sdᴺ([σ])` is a
  span of generators `[σ ∘ a]` over affine subdivision composites `a`.
* `exists_iteratedSubdivision_generator_support_small` — for some `N` every
  affine-summand simplex appearing in `sdᴺ([σ])` is `𝒰`-small.
* `exists_iteratedSubdivision_generator_mem_smallChains` — for some `N`,
  `sdᴺ([σ])` lies in `smallChainSubmodule`.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Finset

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

open AffineBarycentricSubdivision
open BarycentricSubdivisionDiameter

namespace AffineBarycentricSubdivision

/-! ## 1. The affine subdivision map as a genuine linear map -/

/-- The affine subdivision map associated to a permutation `π`, packaged as a
genuine `ℝ`-linear self-map of `Fin (n+1) → ℝ`.  On the standard simplex it
restricts to `affineSubdivMap n π`. -/
noncomputable def affineSubdivLinear (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := fun j => ∑ k : Fin (n + 1), x k * (prefixBarycenter n π k).val j
  map_add' := by
    intro x y; funext j; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  map_smul' := by
    intro c x; funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring

@[simp] theorem affineSubdivLinear_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    affineSubdivLinear n π x j = ∑ k : Fin (n + 1), x k * (prefixBarycenter n π k).val j := rfl

/-
On the standard simplex, the linear map `affineSubdivLinear` restricts to the
affine subdivision map `affineSubdivMap`.
-/
theorem affineSubdivLinear_coe (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineSubdivLinear n π x.val = (affineSubdivMap n π x).val := by
  aesop

/-
The prefix barycenter, as a coordinate vector, equals one barycentric step
applied to the standard vertices.
-/
theorem prefixBarycenter_val_eq_stepVertices (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    (prefixBarycenter n π k).val = stepVertices n (stdVerts n) π k := by
  unfold prefixBarycenter stepVertices;
  ext j; simp +decide [ stdSimplex.map, stdSimplex.barycenter, stdVerts ];
  unfold FunOnFinite.linearMap; simp +decide [ Finset.mul_sum _ _ _ ] ;
  simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite, Pi.single_apply ];
  simp +decide [ Finsupp.sum_fintype, prefixVertex ];
  rw [ ← Finset.sum_subset ( show Finset.image ( fun x : Fin ( k.val + 1 ) => ⟨ x, by linarith [ Fin.is_lt x, Fin.is_lt k ] ⟩ ) Finset.univ ⊆ Finset.Iic k from ?_ ) ];
  · rw [ Finset.sum_image ] <;> norm_num;
    · exact Finset.sum_congr rfl fun _ _ => by rw [ Finsupp.single_apply ] ; aesop;
    · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
  · simp +decide [ Fin.ext_iff ];
    exact fun x hx₁ hx₂ hx₃ => False.elim <| hx₂ ⟨ x, by linarith [ Fin.is_lt x, Fin.is_lt k, show ( x : ℕ ) ≤ k from hx₁ ] ⟩ rfl;
  · exact Finset.image_subset_iff.mpr fun x _ => Finset.mem_Iic.mpr ( Nat.le_trans ( Nat.le_of_lt_succ ( Fin.is_lt x ) ) ( Nat.le_refl _ ) )

/-
`affineSubdivLinear` sends the `k`-th standard vertex to the `k`-th new
barycentric vertex.
-/
theorem affineSubdivLinear_stdVerts (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineSubdivLinear n π (stdVerts n k) = stepVertices n (stdVerts n) π k := by
  ext j; simp +decide [ affineSubdivLinear_apply, stdVerts, Pi.single_apply ] ;
  exact congr_fun ( prefixBarycenter_val_eq_stepVertices n π k ) j

/-! ## 2. Iterated affine subdivision composites -/

/-- The `N`-fold affine subdivision composite as a linear map.  The last
permutation `ρs (last N)` is applied first (innermost), matching the recursion of
`iterVertices`. -/
noncomputable def affineCompLinear (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) →
      ((Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
  | 0, _ => LinearMap.id
  | (N + 1), ρs =>
      (affineCompLinear n N (fun i => ρs i.castSucc)).comp
        (affineSubdivLinear n (ρs (Fin.last N)))

@[simp] theorem affineCompLinear_zero (n : ℕ) (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineCompLinear n 0 ρs = LinearMap.id := rfl

theorem affineCompLinear_succ (n N : ℕ) (ρs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    affineCompLinear n (N + 1) ρs
      = (affineCompLinear n N (fun i => ρs i.castSucc)).comp
          (affineSubdivLinear n (ρs (Fin.last N))) := rfl

/-
**Bridge to Prompt 14.** The composite affine map sends the `k`-th standard
vertex to the `k`-th vertex of the `N`-fold barycentric subdivision sub-simplex
described by `iterVertices`.
-/
theorem affineCompLinear_stdVerts (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineCompLinear n N ρs (stdVerts n k) = iterVertices n N ρs (stdVerts n) k := by
  revert k;
  induction' N with N ih;
  · aesop;
  · intro k
    rw [affineCompLinear_succ, iterVertices_succ];
    convert congr_arg ( fun x => ( affineCompLinear n N fun i => ρs i.castSucc ) x ) ( affineSubdivLinear_stdVerts n ( ρs ( Fin.last N ) ) k ) using 1
    · rfl
    · unfold stepVertices
      simp +decide [ih]

/-- The `N`-fold affine subdivision composite as a continuous self-map of `Δⁿ`. -/
noncomputable def affineCompMap (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) → C(Delta n, Delta n)
  | 0, _ => ContinuousMap.id _
  | (N + 1), ρs =>
      (affineCompMap n N (fun i => ρs i.castSucc)).comp
        (affineSubdivContinuousMap n (ρs (Fin.last N)))

@[simp] theorem affineCompMap_zero (n : ℕ) (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineCompMap n 0 ρs = ContinuousMap.id _ := rfl

theorem affineCompMap_succ (n N : ℕ) (ρs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    affineCompMap n (N + 1) ρs
      = (affineCompMap n N (fun i => ρs i.castSucc)).comp
          (affineSubdivContinuousMap n (ρs (Fin.last N))) := rfl

/-
The continuous composite map agrees, on coordinates, with the linear
composite map.
-/
theorem affineCompMap_coe (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    (affineCompMap n N ρs x).val = affineCompLinear n N ρs x.val := by
  induction' N with N ih generalizing x <;> simp_all +decide [ affineCompMap_succ, affineCompLinear_succ ];
  rw [ ← affineSubdivLinear_coe ]

/-
The `(N+1)`-fold composite obtained by appending `π` as the innermost
subdivision factors as the `N`-fold composite precomposed with `a_π`.
-/
theorem affineCompMap_snoc (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (π : Equiv.Perm (Fin (n + 1))) :
    affineCompMap n (N + 1) (Fin.snoc ρs π)
      = (affineCompMap n N ρs).comp (affineSubdivContinuousMap n π) := by
  -- Unfold the definition of `affineCompMap n (N + 1)` applied to `Fin.snoc ρs π`.
  -- This gives a composition where the outer map is `affineCompMap n N (fun i => (Fin.snoc ρs π) i.castSucc)`
  -- and the inner map is `affineSubdivContinuousMap n ((Fin.snoc ρs π) (Fin.last N))`.
  simp [affineCompMap_succ]

/-! ## 3. Range and diameter of the affine composite -/

/-
The image of `Δⁿ` under the composite affine map is the convex hull of the
`iterVertices` vertex tuple.
-/
theorem range_affineCompMap_val (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    (Subtype.val) '' (Set.range (affineCompMap n N ρs))
      = convexHull ℝ (Set.range (iterVertices n N ρs (stdVerts n))) := by
  have h_range : Set.range (fun x : Delta n => (affineCompMap n N ρs x).val) = (affineCompLinear n N ρs) '' (stdSimplex ℝ (Fin (n + 1))) := by
    ext; simp [affineCompMap_coe];
  convert h_range using 1;
  · exact Set.ext fun x => ⟨ by rintro ⟨ y, ⟨ z, rfl ⟩, rfl ⟩ ; exact ⟨ z, rfl ⟩, by rintro ⟨ z, rfl ⟩ ; exact ⟨ _, ⟨ z, rfl ⟩, rfl ⟩ ⟩;
  · rw [ show stdSimplex ℝ ( Fin ( n + 1 ) ) = convexHull ℝ ( Set.range ( stdVerts n ) ) from ?_ ];
    · rw [ LinearMap.image_convexHull ];
      congr! 1;
      ext; simp [affineCompLinear_stdVerts];
    · change stdSimplex ℝ (Fin (n + 1)) =
        convexHull ℝ (Set.range (fun k : Fin (n + 1) => Pi.single k 1))
      exact (convexHull_rangle_single_eq_stdSimplex ℝ (Fin (n + 1))).symm

/-
The range of the composite affine map has the same diameter as the
`iterVertices` vertex tuple.
-/
theorem diam_range_affineCompMap (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (affineCompMap n N ρs))
      = Metric.diam (Set.range (iterVertices n N ρs (stdVerts n))) := by
  rw [ ← isometry_subtype_coe.diam_image ];
  rw [ range_affineCompMap_val, convexHull_diam ]

/-- For every `ε > 0` there is `N` such that the range of *every* `N`-fold affine
subdivision composite has diameter `< ε`. -/
theorem exists_diam_range_affineCompMap_lt (n : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
      Metric.diam (Set.range (affineCompMap n N ρs)) < eps := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_affine_diameter_lt n eps heps
  exact ⟨N, fun ρs => by rw [diam_range_affineCompMap]; exact hN ρs⟩

/-! ## 4. The affine-summand singular simplex -/

variable {X : TopCat.{0}}

/-- The singular simplex `σ ∘ a` where `a = affineCompMap n N ρs`; these are
exactly the simplices appearing in the support of `sdᴺ([σ])`. -/
noncomputable def affineSummandSimplex (n N : ℕ) (σ : singularSimplices X n)
    (ρs : Fin N → Equiv.Perm (Fin (n + 1))) : singularSimplices X n :=
  continuousMapAsSingularSimplex X n ((mvSimplexMap σ).comp (affineCompMap n N ρs))

/-- The continuous map underlying `affineSummandSimplex` is `σ ∘ a`. -/
@[simp] theorem mvSimplexMap_affineSummandSimplex (n N : ℕ) (σ : singularSimplices X n)
    (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    mvSimplexMap (affineSummandSimplex n N σ ρs)
      = (mvSimplexMap σ).comp (affineCompMap n N ρs) := by
  simp only [affineSummandSimplex, mvSimplexMap, singularSimplexAsContinuousMap,
    continuousMapAsSingularSimplex, Equiv.apply_symm_apply]

/-
The `N = 0` summand simplex is `σ` itself.
-/
theorem affineSummandSimplex_zero (n : ℕ) (σ : singularSimplices X n)
    (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineSummandSimplex n 0 σ ρs = σ := by
  exact singularSimplices_ext rfl

/-
One barycentric subdivision summand of an affine-summand simplex is again an
affine-summand simplex, with one more (innermost) permutation factor.
-/
theorem barycentricSubdivSimplex_affineSummandSimplex (n N : ℕ)
    (σ : singularSimplices X n) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (π : Equiv.Perm (Fin (n + 1))) :
    barycentricSubdivSimplex X n π (affineSummandSimplex n N σ ρs)
      = affineSummandSimplex n (N + 1) σ (Fin.snoc ρs π) := by
  unfold barycentricSubdivSimplex affineSummandSimplex;
  unfold affineCompMap; aesop;

/-! ## 5. The support / generator expansion of `sdᴺ([σ])` -/

/-
`sd^(N+1)` applied degree-wise equals `sd` applied after `sd^N`.
-/
theorem barycentricSubdivisionIterLinearMap_succ' (R : Type) [CommRing R] (X : TopCat.{0})
    (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (N + 1) n c
      = (barycentricSubdivisionLinearMap R X n).hom
          (barycentricSubdivisionIterLinearMap R X N n c) := by
  induction' N with N ih generalizing c;
  · rw [barycentricSubdivisionIterLinearMap_succ,
      barycentricSubdivisionIterLinearMap_zero,
      barycentricSubdivisionIterLinearMap_zero]
  · rw [barycentricSubdivisionIterLinearMap_succ, ih,
      barycentricSubdivisionIterLinearMap_succ]

/-
**Support / generator expansion.** `sdᴺ([σ])` lies in the `R`-span of the
generators of the affine-summand simplices `σ ∘ a`.
-/
theorem support_iteratedSubdivision_generator_subset_affineSummands
    (R : Type) [CommRing R] (n N : ℕ) (σ : singularSimplices X n) :
    barycentricSubdivisionIterLinearMap R X N n (chainGenerator R X n σ)
      ∈ Submodule.span R
          {c | ∃ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
            chainGenerator R X n (affineSummandSimplex n N σ ρs) = c} := by
  induction' N with N ih generalizing σ;
  · refine' Submodule.subset_span ⟨ fun _ => Equiv.refl _, _ ⟩;
    rw [ barycentricSubdivisionIterLinearMap_zero, affineSummandSimplex_zero ];
  · rw [ barycentricSubdivisionIterLinearMap_succ' ];
    refine' Submodule.span_induction _ _ _ _ ( ih σ );
    · intro c hc
      obtain ⟨ρs, rfl⟩ := hc
      simp [barycentricSubdivisionLinearMap_generator_sum,
        barycentricSubdivSimplex_affineSummandSimplex];
      exact Submodule.sum_mem _ fun π _ => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ _, rfl ⟩ );
    · simp +decide [ ModuleCat.Hom.hom ];
    · simp +contextual [ map_add ];
      exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy';
    · simp +contextual [ Submodule.smul_mem ]

/-! ## 6. Smallness and small-chain membership -/

/-
**Support-level smallness.** For some `N`, every affine-summand simplex
appearing in `sdᴺ([σ])` is `𝒰`-small.
-/
theorem exists_iteratedSubdivision_generator_support_small
    (𝒰 : OpenCoverData X) (n : ℕ) (σ : singularSimplices X n) :
    ∃ N : ℕ, ∀ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
      IsSmallSimplex 𝒰 (affineSummandSimplex n N σ ρs) := by
  obtain ⟨ eps, heps ⟩ := singularSimplex_hasLebesgueNumber_for_openCover 𝒰 σ;
  obtain ⟨ N, hN ⟩ := exists_diam_range_affineCompMap_lt n eps heps.1;
  use N;
  intro ρs
  obtain ⟨ U, hU₁, hU₂ ⟩ := heps.2 (Set.range (affineCompMap n N ρs)) (hN ρs);
  use U, hU₁;
  convert hU₂ using 1;
  simp +decide [ Set.range_comp ]

/-
**Main deliverable.** Some iterated barycentric subdivision of the generator
`[σ]` lies in the submodule of `𝒰`-small chains.
-/
theorem exists_iteratedSubdivision_generator_mem_smallChains
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ) (σ : singularSimplices X n) :
    ∃ N : ℕ,
      barycentricSubdivisionIterLinearMap R X N n (chainGenerator R X n σ)
        ∈ smallChainSubmodule R X 𝒰 n := by
  obtain ⟨ N, hN ⟩ := exists_iteratedSubdivision_generator_support_small 𝒰 n σ;
  use N;
  refine' Submodule.span_le.mpr _ ( support_iteratedSubdivision_generator_subset_affineSummands R n N σ );
  exact fun x hx => by obtain ⟨ ρs, rfl ⟩ := hx; exact chainGenerator_mem_smallChainSubmodule ( hN ρs ) ;

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
