import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.CrossedProductCovariant

/-!
# The reduced crossed product `A ⋊_r G`

Lane TWWUCT-A (work order WO-TWWUCT-A), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).  Following Brown--Ozawa, Def. 4.1.4,
and Williams, §7.2, the reduced crossed product is the norm closure of the image
of the integrated form of the regular covariant pair built from a faithful
representation of `A` (here `faithfulRep A`):

* `algCrossedProduct G A`: the image of `C_c(G, A) = G →₀ A`, a non-unital
  `⋆`-subalgebra of `B(ℓ²(G, H_A))`;
* `ReducedCrossedProduct G A`: its closure, a non-unital C⋆-algebra;
* it is separable when `G` is countable and `A` is separable;
* `ReducedCrossedProduct.of G A : (G →₀ A) →ₗ[ℂ] A ⋊_r G`, with dense range and the
  convolution and involution formulas on generators.

`CrossedProductNorm` shows that the norm does not depend on the faithful representation.
-/

namespace GroupApproximation.Full.TWWUCT

open CrossedProduct

universe u v

noncomputable section

variable (G : Type u) [Group G] (A : Type v) [NonUnitalCStarAlgebra A] [GCStarAlgebra G A]

/-- **The algebraic crossed product** `C_c(G, A)` in the regular representation:
the range of the integrated form of the regular covariant pair induced by
`faithfulRep A` (Brown--Ozawa §4.1).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
def algCrossedProduct :
    NonUnitalStarSubalgebra ℂ (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A)) :=
  { LinearMap.range (integrate (G := G) (faithfulRep A)) with
    mul_mem' := fun {S T} hS hT => by
      obtain ⟨x, rfl⟩ := (LinearMap.mem_range (f := integrate (G := G) (faithfulRep A))).1 hS
      obtain ⟨y, rfl⟩ := (LinearMap.mem_range (f := integrate (G := G) (faithfulRep A))).1 hT
      exact integrate_mul_mem (faithfulRep A) x y
    star_mem' := fun {S} hS => by
      obtain ⟨x, rfl⟩ := (LinearMap.mem_range (f := integrate (G := G) (faithfulRep A))).1 hS
      exact star_integrate_mem (faithfulRep A) x }

theorem mem_algCrossedProduct (T : L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A)) :
    T ∈ algCrossedProduct G A ↔ T ∈ LinearMap.range (integrate (G := G) (faithfulRep A)) :=
  Iff.rfl

/-- The closure of `algCrossedProduct G A` in `B(ℓ²(G, H_A))`. -/
def reducedCrossedProductSubalgebra :
    NonUnitalStarSubalgebra ℂ (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A)) :=
  (algCrossedProduct G A).topologicalClosure

/-- **The reduced crossed product** `A ⋊_r G` (Brown--Ozawa, Def. 4.1.4; Williams, §7.2).
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
abbrev ReducedCrossedProduct : Type (max u v) :=
  reducedCrossedProductSubalgebra G A

instance instNonUnitalCStarAlgebraReducedCrossedProduct :
    NonUnitalCStarAlgebra (ReducedCrossedProduct G A) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (reducedCrossedProductSubalgebra G A)
    (h_closed := NonUnitalStarSubalgebra.isClosed_topologicalClosure (algCrossedProduct G A))

theorem integrate_mem_span_range_genLinear (x : G →₀ A) :
    integrate (G := G) (faithfulRep A) x ∈
      Submodule.span ℂ (⋃ g : G, Set.range (genLinear (G := G) (faithfulRep A) g)) := by
  induction x using Finsupp.induction_linear with
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂
  | single g a =>
    rw [integrate_single]
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨g, a, rfl⟩)

/-- **Separability** of `A ⋊_r G` for countable `G` and separable `A`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
instance instSeparableSpaceReducedCrossedProduct [Countable G]
    [TopologicalSpace.SeparableSpace A] :
    TopologicalSpace.SeparableSpace (ReducedCrossedProduct G A) := by
  have hgen : ∀ g : G, TopologicalSpace.IsSeparable
      (Set.range (genLinear (G := G) (faithfulRep A) g)) := fun g =>
    TopologicalSpace.isSeparable_range
      (AddMonoidHomClass.continuous_of_bound (genLinear (G := G) (faithfulRep A) g) 1
        fun a => by
          rw [one_mul]
          exact norm_gen_le (faithfulRep A) a g)
  have hspan := TopologicalSpace.IsSeparable.span (R := ℂ)
    (TopologicalSpace.IsSeparable.iUnion hgen)
  have hsub : (algCrossedProduct G A :
      Set (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A))) ⊆
        (Submodule.span ℂ (⋃ g : G, Set.range (genLinear (G := G) (faithfulRep A) g)) :
          Set (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A))) := by
    intro T hT
    obtain ⟨x, rfl⟩ := (LinearMap.mem_range (f := integrate (G := G) (faithfulRep A))).1 hT
    exact integrate_mem_span_range_genLinear G A x
  have hcl : TopologicalSpace.IsSeparable (reducedCrossedProductSubalgebra G A :
      Set (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A))) :=
    (hspan.mono hsub).closure
  exact hcl.separableSpace

namespace ReducedCrossedProduct

theorem integrate_mem (x : G →₀ A) :
    integrate (G := G) (faithfulRep A) x ∈ reducedCrossedProductSubalgebra G A :=
  NonUnitalStarSubalgebra.le_topologicalClosure (algCrossedProduct G A)
    ((mem_algCrossedProduct G A _).2 (LinearMap.mem_range_self _ x))

/-- **The canonical map** `C_c(G, A) → A ⋊_r G`, `∑ a_g δ_g ↦ ∑ π̃(a_g) λ_g`.
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
def of : (G →₀ A) →ₗ[ℂ] ReducedCrossedProduct G A where
  toFun x := ⟨integrate (G := G) (faithfulRep A) x, integrate_mem G A x⟩
  map_add' x y := Subtype.ext (map_add (integrate (G := G) (faithfulRep A)) x y)
  map_smul' c x := Subtype.ext (map_smul (integrate (G := G) (faithfulRep A)) c x)

theorem coe_of (x : G →₀ A) :
    (of G A x : L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A)) =
      integrate (G := G) (faithfulRep A) x :=
  rfl

variable {G A}

theorem of_single_mul_of_single (g h : G) (a b : A) :
    of G A (Finsupp.single g a) * of G A (Finsupp.single h b) =
      of G A (Finsupp.single (g * h) (a * GCStarAlgebra.act (A := A) g b)) := by
  apply Subtype.ext
  change integrate (faithfulRep A) (Finsupp.single g a) *
      integrate (faithfulRep A) (Finsupp.single h b) =
    integrate (faithfulRep A) (Finsupp.single (g * h) (a * GCStarAlgebra.act (A := A) g b))
  rw [integrate_single, integrate_single, integrate_single, gen_mul_gen]

theorem star_of_single (g : G) (a : A) :
    star (of G A (Finsupp.single g a)) =
      of G A (Finsupp.single g⁻¹ (GCStarAlgebra.act (A := A) g⁻¹ (star a))) := by
  apply Subtype.ext
  change star (integrate (faithfulRep A) (Finsupp.single g a)) =
    integrate (faithfulRep A) (Finsupp.single g⁻¹ (GCStarAlgebra.act (A := A) g⁻¹ (star a)))
  rw [integrate_single, integrate_single, star_gen]

variable (G A)

/-- `C_c(G, A)` is dense in `A ⋊_r G`. -/
theorem denseRange_of : DenseRange (of G A) := by
  intro y
  rw [closure_subtype]
  have hy : (y : L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A)) ∈
      closure (algCrossedProduct G A :
        Set (L2 G (FaithfulSpace A) →L[ℂ] L2 G (FaithfulSpace A))) := y.2
  refine closure_mono ?_ hy
  intro T hT
  obtain ⟨x, rfl⟩ := (LinearMap.mem_range (f := integrate (G := G) (faithfulRep A))).1 hT
  exact ⟨of G A x, ⟨x, rfl⟩, rfl⟩

end ReducedCrossedProduct

end

end GroupApproximation.Full.TWWUCT
