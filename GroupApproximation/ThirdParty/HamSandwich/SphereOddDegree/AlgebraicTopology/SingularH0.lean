import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubChainSubspaceBridge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone

/-!
# Zeroth singular homology of path-connected spaces

We build the classical computation `H₀(X; ℤ) ≅ ℤ` for a nonempty path-connected
space `X`, via the augmentation `ε : C₀(X) → ℤ` (sum of coefficients).  The key
geometric input is that for points joined by a path, the difference of the two
`0`-simplices is a boundary (`chainGenerator_sub_mem_range_of_path`).
-/

open CategoryTheory AlgebraicTopology Limits
open AffineBarycentricSubdivision

noncomputable section
namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

variable {X : TopCat.{0}}

/-- The `0`-simplex of `X` sitting at the point `x`. -/
noncomputable def pointSimplex (X : TopCat.{0}) (x : X) : singularSimplices X 0 :=
  continuousMapAsSingularSimplex X 0 (ContinuousMap.const (Delta 0) x)

/-- The singular `1`-simplex of `X` obtained from a path, by reparametrising the
standard `1`-simplex `Δ¹` as the unit interval. -/
noncomputable def pathSimplex {a b : X} (p : Path a b) : singularSimplices X 1 :=
  continuousMapAsSingularSimplex X 1
    (p.toContinuousMap.comp
      (⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩ :
        C(Delta 1, unitInterval)))

/-
The boundary of the path `1`-simplex is the difference of its endpoint
`0`-simplices.
-/
theorem boundary_pathSimplex {a b : X} (p : Path a b) :
    (singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 (pathSimplex p))
      = chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a) := by
  simp +decide [ singularBoundary_chainGenerator_formula ];
  rw [ show AlexanderWhitney.faceSimplex X 0 0 ( pathSimplex p ) = pointSimplex X b from ?_, show AlexanderWhitney.faceSimplex X 0 1 ( pathSimplex p ) = pointSimplex X a from ?_ ] ; abel1;
  · apply singularSimplices_ext;
    ext x;
    convert congr_arg ( fun x => ( p.toContinuousMap.comp ( stdSimplexHomeomorphUnitInterval ) ) x ) ( show ( cofaceTop 0 1 x ) = ( ⟨ _, single_mem_stdSimplex ℝ 0 ⟩ : Delta 1 ) from ?_ ) using 1;
    · convert p.source.symm using 1;
    · convert delta0_subsingleton x ( stdSimplex.vertex 0 );
      constructor <;> intro h <;> simp_all +decide [ cofaceTop ];
      convert delta0_subsingleton x ( stdSimplex.vertex 0 );
  · apply singularSimplices_ext;
    ext x;
    convert congr_arg p ( stdSimplexHomeomorphUnitInterval_one ) using 1;
    · convert congr_arg p ( show stdSimplexHomeomorphUnitInterval ( cofaceTop 0 0 x ) = 1 from ?_ ) using 1;
      convert stdSimplexHomeomorphUnitInterval_one using 1;
      congr;
      ext i; fin_cases i ; simp +decide [ cofaceTop ] ;
      · simp +decide [ FunOnFinite.linearMap ];
        simp +decide [ Finsupp.mapDomain ];
      · simp +decide [ cofaceTop ];
        simp +decide [ FunOnFinite.linearMap ];
        simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite ];
        simp +decide [ Finsupp.sum_fintype, Finsupp.single_apply ];
    · convert p.target.symm using 1

/-- For points joined by a path, the difference of the corresponding `0`-simplex
generators is a boundary. -/
theorem chainGenerator_sub_mem_range_of_path {a b : X} (p : Path a b) :
    chainGenerator ℤ X 0 (pointSimplex X b) - chainGenerator ℤ X 0 (pointSimplex X a)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom :=
  ⟨chainGenerator ℤ X 1 (pathSimplex p), boundary_pathSimplex p⟩

/-
For points in the same (path-)connected space, the difference of their
`0`-simplex generators is a boundary.
-/
theorem chainGenerator_sub_mem_range [PathConnectedSpace X] (σ τ : singularSimplices X 0) :
    chainGenerator ℤ X 0 σ - chainGenerator ℤ X 0 τ
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
        have h_simplices : ∃ a b : X, σ = pointSimplex X a ∧ τ = pointSimplex X b := by
          refine' ⟨ _, _, _, _ ⟩;
          exact ( singularSimplexAsContinuousMap X 0 σ ) ( stdSimplex.vertex 0 );
          exact ( singularSimplexAsContinuousMap X 0 τ ) ( stdSimplex.vertex 0 );
          · apply singularSimplices_ext;
            ext x;
            convert congr_arg ( fun y => ( singularSimplexAsContinuousMap X 0 σ ) y ) ( delta0_subsingleton x ( stdSimplex.vertex 0 ) ) using 1;
          · apply singularSimplices_ext;
            exact ContinuousMap.ext fun x => by rw [ show x = stdSimplex.vertex 0 from delta0_subsingleton _ _ ] ; rfl;
        obtain ⟨ a, b, rfl, rfl ⟩ := h_simplices;
        have := chainGenerator_sub_mem_range_of_path ( PathConnectedSpace.somePath b a ) ; aesop;

/-! ## The augmentation -/

/-- The augmentation `ε : C₀(X; ℤ) → ℤ` summing the coefficients (each `0`-simplex
generator maps to `1`). -/
noncomputable def aug (X : TopCat.{0}) : singularChainGroup ℤ X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Limits.Sigma.desc (fun _ => 𝟙 (ModuleCat.of ℤ ℤ))

@[simp] theorem aug_generator (σ : singularSimplices X 0) :
    (aug X).hom (chainGenerator ℤ X 0 σ) = 1 := by
      convert congr_arg ( fun f : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => ( ModuleCat.Hom.hom f ) 1 ) ( show ( Limits.Sigma.ι ( fun _ => ModuleCat.of ℤ ℤ ) σ ≫ Limits.Sigma.desc ( fun _ => 𝟙 ( ModuleCat.of ℤ ℤ ) ) : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ ) = 𝟙 ( ModuleCat.of ℤ ℤ ) from ?_ ) using 1;
      simp +decide [ CategoryTheory.Limits.colimit.ι_desc ]

theorem aug_boundary (c : singularChainGroup ℤ X 1) :
    (aug X).hom ((singularBoundary ℤ X 0).hom c) = 0 := by
      refine' Submodule.span_induction _ _ _ _ ( show c ∈ Submodule.span ℤ ( Set.range ( fun τ : singularSimplices X 1 => chainGenerator ℤ X 1 τ ) ) from _ );
      · exact Submodule.mem_sInf.mpr (by
        intro p hp;
        convert p.span_le.mpr hp ( show c ∈ Submodule.span ℤ ( Set.range fun τ : singularSimplices X 1 => chainGenerator ℤ X 1 τ ) from ?_ ) using 1;
        convert Submodule.mem_top;
        grind +suggestions);
      · intro x hx
        obtain ⟨τ, rfl⟩ := hx
        have h_sum : (aug X).hom ((singularBoundary ℤ X 0).hom (chainGenerator ℤ X 1 τ)) = 0 := by
          rw [ singularBoundary_chainGenerator_formula ] ; simp +decide [ Fin.sum_univ_two ] ;
          rw [ aug_generator, aug_generator ] ; norm_num
        exact h_sum;
      · aesop;
      · aesop;
      · simp +contextual [ map_smul ]

/-
Every `0`-chain is, modulo boundaries, `ε(c)` copies of a fixed basepoint
`0`-simplex.
-/
theorem sub_aug_smul_basept_mem_range [PathConnectedSpace X] (b : X)
    (c : singularChainGroup ℤ X 0) :
    c - (aug X).hom c • chainGenerator ℤ X 0 (pointSimplex X b)
      ∈ LinearMap.range (singularBoundary ℤ X 0).hom := by
        -- Work additively: the basis chains generate the chain group as an additive
        -- subgroup, so we may induct over `AddSubgroup.closure`, avoiding the
        -- scalar-action instance diamond on the `ModuleCat ℤ` carrier.
        have h_span : c ∈ AddSubgroup.closure (Set.range (chainGenerator ℤ X 0)) := by
          have hc0 : c ∈ Submodule.span ℤ (Set.range (chainGenerator ℤ X 0)) := by
            rw [chainGenerator_span_top]; exact Submodule.mem_top
          induction hc0 using Submodule.span_induction with
          | mem y hy => exact AddSubgroup.subset_closure hy
          | zero => exact zero_mem _
          | add p q _ _ hp hq => exact add_mem hp hq
          | smul r a _ ha => convert zsmul_mem ha r using 1; exact int_smul_eq_zsmul _ r a
        induction h_span using AddSubgroup.closure_induction with
        | mem c hc =>
            obtain ⟨σ, rfl⟩ := hc
            rw [aug_generator, one_zsmul]
            exact chainGenerator_sub_mem_range σ (pointSimplex X b)
        | zero => simp
        | add x y _ _ hx hy =>
            have h : x + y - (aug X).hom (x + y) • chainGenerator ℤ X 0 (pointSimplex X b)
                = (x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b))
                  + (y - (aug X).hom y • chainGenerator ℤ X 0 (pointSimplex X b)) := by
              rw [map_add, add_zsmul]; abel
            rw [h]; exact Submodule.add_mem _ hx hy
        | neg x _ hx =>
            have h : -x - (aug X).hom (-x) • chainGenerator ℤ X 0 (pointSimplex X b)
                = -(x - (aug X).hom x • chainGenerator ℤ X 0 (pointSimplex X b)) := by
              rw [map_neg, neg_zsmul]; abel
            rw [h]; exact Submodule.neg_mem _ hx

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
