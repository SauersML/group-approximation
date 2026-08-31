import Mathlib
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SmallChainComplex
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.IteratedSubdivisionHomotopySmall
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionIter
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SmallChainsHomologySurjectivity

/-!
# The small-chain inclusion is injective on homology

For an open cover `𝒰` of a space `X`, this file proves that the inclusion chain
map `smallChainsInclusion R X 𝒰 : C_*^𝒰(X; R) ⟶ C_*(X; R)` of small singular
chains into all singular chains induces an **injection on homology** in every
degree.

## Mathematical proof

Let `z` be a small `n`-cycle whose image in full singular homology is zero.  Then
there is a full chain `b ∈ C_{n+1}(X)` with `∂ b = z`.  We must subdivide `b` to
make it small while correcting by the subdivision homotopy.

Choose two thresholds independently and combine them by `max`/monotonicity:

* `N₁` so that the iterated subdivision `sd^{N₁} b` is small
  (`exists_iteratedSubdivision_chain_mem_smallChains`);
* `N₂` so that the accumulated homotopy chain `H^{N₂} z` is small (here every `N₂`
  works because `z` is already small and `H^(N)` preserves small chains,
  `iteratedSubdivisionHomotopy_preserves_smallChains`).

Set `N := max N₁ N₂`; by `sdIter_mem_smallChainSubmodule_mono` (and preservation)
both `sd^N b` and `H^N z` are small.  Put `bSmall := sd^N b` and `hSmall := H^N z`.

Since subdivision commutes with the boundary, `∂ (sd^N b) = sd^N(∂ b) = sd^N z`,
and the iterated-subdivision boundary formula
(`barycentricSubdivisionIter_boundary_formula`), using `∂ z = 0` (which holds
because `z = ∂ b` is a boundary, so `∂ z = ∂ ∂ b = 0`), gives
`z - sd^N z = ∂ (H^N z)`.  Adding `sd^N z = ∂ (sd^N b)` yields **Prompt 10's
formula**

```text
z = ∂ (bSmall + hSmall),
```

a boundary of a *small* `(n+1)`-chain.  Therefore the class of `z` is already zero
in the small-chain homology, proving injectivity.

## Main results

* `SphereOddDegree.exists_d_eq_iCycles_of_homologyπ_zero` — a cycle whose homology
  class vanishes is the boundary of some chain (kernel/cokernel presentation of
  homology for `ModuleCat`-valued chain complexes).
* `SphereOddDegree.homologyπ_zero_of_iCycles_eq_d` — conversely, a cycle that
  bounds has vanishing homology class.
* `SphereOddDegree.exists_small_boundary_witness` — the `max`/monotonicity
  combination producing a *small* `(n+1)`-chain `bChain` with
  `∂ bChain = ∂ b` (Prompt 10's formula `z = ∂(bSmall + hSmall)`).
* `SphereOddDegree.smallChainsInclusion_injective_on_homology` — the inclusion of
  small chains is injective on homology in every degree.
-/

open CategoryTheory AlgebraicTopology
open AffineBarycentricSubdivision

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-! ## 1. Kernel/cokernel presentation of homology -/

/-- **Cokernel presentation, forward direction.**  In a `ModuleCat`-valued chain
complex, a cycle `W` whose homology class `homologyπ W` vanishes is the boundary
of some chain: there is `b` with `∂ b = iCycles W`. -/
theorem exists_d_eq_iCycles_of_homologyπ_zero
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (W : K.cycles n)
    (h : (K.homologyπ n).hom W = 0) :
    ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = (K.iCycles n).hom W := by
  -- `homologyπ` is the cokernel of `toCycles`, so `W` lies in the image of `toCycles`.
  have hW_im : ∃ b : K.X (n + 1), (K.toCycles (n + 1) n).hom b = W := by
    have := HomologicalComplex.homologyIsCokernel K ( n + 1 ) n ( by simp +decide [ ComplexShape.prev ] );
    replace := this.existsUnique;
    obtain ⟨ d, hd₁, hd₂ ⟩ := this ( Limits.CokernelCofork.ofπ ( ModuleCat.ofHom ( Submodule.mkQ ( LinearMap.range ( K.toCycles ( n + 1 ) n ).hom ) ) ) ( by aesop ) );
    have := hd₁ Limits.WalkingParallelPair.one; simp_all +decide ;
    replace this := congr_arg ( fun f => f.hom W ) this; simp_all +decide ;
    rw [ eq_comm, Submodule.Quotient.mk_eq_zero ] at this;
    exact this;
  obtain ⟨ b, hb ⟩ := hW_im; use b;
  rw [ ← hb ];
  convert congr_arg ( fun f => f.hom b ) ( HomologicalComplex.toCycles_i K ( n + 1 ) n ) using 1;
  · grind +suggestions;
  · exact congr_arg ( fun f => f.hom b ) ( HomologicalComplex.toCycles_i K ( n + 1 ) n )

/-- **Cokernel presentation, backward direction.**  In a `ModuleCat`-valued chain
complex, a cycle `W` whose underlying chain is the boundary of some chain `b`
(`iCycles W = ∂ b`) has vanishing homology class. -/
theorem homologyπ_zero_of_iCycles_eq_d
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) (W : K.cycles n) (b : K.X (n + 1))
    (h : (K.iCycles n).hom W = (K.d (n + 1) n).hom b) :
    (K.homologyπ n).hom W = 0 := by
  -- Since `iCycles` is injective and `toCycles ≫ iCycles = d`, `W = toCycles b`.
  have hW : W = (K.toCycles (n + 1) n).hom b := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have ht := congr_arg (fun f => f.hom b) (HomologicalComplex.toCycles_i K (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
    rw [h, ht]
  rw [hW]
  -- And `toCycles ≫ homologyπ = 0`.
  have hc := congrArg (fun m => m.hom b)
    (HomologicalComplex.toCycles_comp_homologyπ K (n + 1) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at hc
  exact hc

/-- The `H^(N)(∂ ·)` term of the iterated-subdivision boundary formula vanishes on a
full singular cycle `z`. -/
theorem iterHomotopyBoundaryTerm_eq_zero_of_full_cycle
    (R : Type) [CommRing R] (X : TopCat.{0}) (N n : ℕ)
    (z : singularChainGroup R X n)
    (hz : ((singularChainComplex R X).d n ((ComplexShape.down ℕ).next n)).hom z = 0) :
    barycentricSubdivisionIterHomotopyBoundaryTerm R X N n z = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [barycentricSubdivisionIterHomotopyBoundaryTerm_succ]
    rw [ComplexShape.next_eq' (ComplexShape.down ℕ) (j := n) rfl] at hz
    have hz' : (singularBoundary R X n).hom z = 0 := hz
    rw [hz', map_zero]

/-! ## 2. The small boundary witness (Prompt 10's formula via max/monotonicity) -/

/-
**Prompt 10's formula via `max`/monotonicity.**  Let `b` be an `(n+1)`-chain
whose boundary `z = ∂ b` is small.  Then there is a *small* `(n+1)`-chain `bChain`
with `∂ bChain = ∂ b`.

`bChain = bSmall + hSmall` where `bSmall = sd^N b` and `hSmall = H^N z`, and `N`
is obtained as the `max` of an `N₁` shrinking `b` and an `N₂` controlling the
homotopy term, lifted to `N` by monotonicity.
-/
theorem exists_small_boundary_witness
    (𝒰 : OpenCoverData X) (R : Type) [CommRing R] (n : ℕ)
    (b : singularChainGroup R X (n + 1))
    (hsmall : (singularBoundary R X n).hom b ∈ smallChainSubmodule R X 𝒰 n) :
    ∃ bChain : singularChainGroup R X (n + 1),
      bChain ∈ smallChainSubmodule R X 𝒰 (n + 1) ∧
      (singularBoundary R X n).hom bChain = (singularBoundary R X n).hom b := by
  -- `z = ∂ b` is a cycle (`∂ ∂ b = 0`), so the homotopy boundary term will vanish.
  have hcyc : ((singularChainComplex R X).d n ((ComplexShape.down ℕ).next n)).hom
      ((singularBoundary R X n).hom b) = 0 := by
    have hdd := congrArg (fun m => m.hom b)
      ((singularChainComplex R X).d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hdd
    exact hdd
  -- `N₁`: an iterate after which the subdivision of `b` is small.
  obtain ⟨N₁, hN₁⟩ := exists_iteratedSubdivision_chain_mem_smallChains 𝒰 R (n + 1) b
  -- `N₂`: an iterate after which the homotopy term `H^{N₂} z` is small (every `N₂`
  -- works since `z = ∂ b` is small and `H^(N)` preserves small chains).
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ,
      barycentricSubdivisionIterHomotopyLinearMap R X N₂ n ((singularBoundary R X n).hom b)
        ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    ⟨0, iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 0 n _ hsmall⟩
  -- Combine the two thresholds by `max`, lifting each smallness via monotonicity.
  have hbN : barycentricSubdivisionIterLinearMap R X (max N₁ N₂) (n + 1) b
      ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    sdIter_mem_smallChainSubmodule_mono R 𝒰 (le_max_left N₁ N₂) hN₁
  have hHN : barycentricSubdivisionIterHomotopyLinearMap R X (max N₁ N₂) n
      ((singularBoundary R X n).hom b) ∈ smallChainSubmodule R X 𝒰 (n + 1) :=
    iteratedSubdivisionHomotopy_preserves_smallChains R 𝒰 (max N₁ N₂) n _ hsmall
  -- `bChain = bSmall + hSmall` with `bSmall = sd^N b` and `hSmall = H^N z`.
  refine ⟨barycentricSubdivisionIterLinearMap R X (max N₁ N₂) (n + 1) b
      + barycentricSubdivisionIterHomotopyLinearMap R X (max N₁ N₂) n
          ((singularBoundary R X n).hom b),
      Submodule.add_mem _ hbN hHN, ?_⟩
  -- `∂ bSmall = sd^N z` (subdivision commutes with `∂`).
  have hcomm := barycentricSubdivisionIterLinearMap_commutes_boundary R X (max N₁ N₂) n b
  -- Boundary formula at `z`, with the homotopy boundary term killed by `hcyc`.
  have hbf := barycentricSubdivisionIter_boundary_formula R X (max N₁ N₂) n
    ((singularBoundary R X n).hom b)
  rw [iterHomotopyBoundaryTerm_eq_zero_of_full_cycle R X (max N₁ N₂) n _ hcyc, add_zero] at hbf
  -- `z = ∂(bSmall + hSmall) = sd^N z + (z - sd^N z)`.
  rw [map_add, hcomm, ← hbf]
  abel

/-! ## 3. Injectivity on homology -/

/-
**The inclusion of small chains is injective on homology** in every degree.
-/
theorem smallChainsInclusion_injective_on_homology
    (R : Type) [CommRing R] (X : TopCat.{0}) (𝒰 : OpenCoverData X) (n : ℕ) :
    Function.Injective (homologyMapInDegree (smallChainsInclusion R X 𝒰) n) := by
  intro x y hxy
  obtain ⟨w, hw⟩ : ∃ w : (smallChainComplex R X 𝒰).cycles n, (smallChainComplex R X 𝒰).homologyπ n w = x - y := by
    have := homologyπ_surjective ( smallChainComplex R X 𝒰 ) n ( x - y ) ; aesop;
  -- By naturality of the homology map, we have $(F.homologyπ n).hom ((S.cyclesMap ι n).hom w) = 0$.
  have hWfull : (singularChainComplex R X).homologyπ n ((smallChainComplex R X 𝒰).cyclesMap (smallChainsInclusion R X 𝒰) n w) = 0 := by
    have hWfull : (singularChainComplex R X).homologyπ n ((smallChainComplex R X 𝒰).cyclesMap (smallChainsInclusion R X 𝒰) n w) = (HomologicalComplex.homologyMap (smallChainsInclusion R X 𝒰) n).hom ((smallChainComplex R X 𝒰).homologyπ n w) := by
      convert congr_arg ( fun m => m w ) ( HomologicalComplex.homologyπ_naturality ( smallChainsInclusion R X 𝒰 ) n ) using 1;
      · simp +decide [ HomologicalComplex.homologyπ_naturality ];
      · convert congr_arg ( fun m => m w ) ( HomologicalComplex.homologyπ_naturality ( smallChainsInclusion R X 𝒰 ) n ) using 1;
    simp_all +decide [ homologyMapInDegree ];
  -- By `exists_d_eq_iCycles_of_homologyπ_zero`, there exists `b : F.X (n+1)` such that `(F.d (n+1) n).hom b = (F.iCycles n).hom ((S.cyclesMap ι n).hom w)`.
  obtain ⟨b, hb⟩ : ∃ b : singularChainGroup R X (n + 1), (singularBoundary R X n).hom b = (smallChainsInclusion R X 𝒰).f n ((smallChainComplex R X 𝒰).iCycles n w) := by
    convert exists_d_eq_iCycles_of_homologyπ_zero ( singularChainComplex R X ) n _ hWfull using 1;
    ext; simp +decide ;
    convert Iff.rfl;
    convert congr_arg ( fun f => f w ) ( HomologicalComplex.cyclesMap_i ( smallChainsInclusion R X 𝒰 ) n ) using 1;
  -- By `exists_small_boundary_witness`, there exists `bChain : singularChainGroup R X (n+1)` such that `bChain ∈ smallChainSubmodule R X 𝒰 (n+1)` and `(singularBoundary R X n).hom bChain = (singularBoundary R X n).hom b`.
  obtain ⟨bChain, hbChain_mem, hbChain_eq⟩ : ∃ bChain : singularChainGroup R X (n + 1), bChain ∈ smallChainSubmodule R X 𝒰 (n + 1) ∧ (singularBoundary R X n).hom bChain = (singularBoundary R X n).hom b := by
    apply exists_small_boundary_witness
    rw [hb]
    exact ((smallChainComplex R X 𝒰).iCycles n w).2
  -- Form `bSmall : smallChainSubmodule R X 𝒰 (n+1) := ⟨bChain, hbChain_mem⟩`.
  set bSmall : smallChainSubmodule R X 𝒰 (n + 1) := ⟨bChain, hbChain_mem⟩;
  -- Show `(S.iCycles n).hom w = (S.d (n+1) n).hom bSmall`.
  have h_eq : (smallChainComplex R X 𝒰).iCycles n w = (smallChainComplex R X 𝒰).d (n + 1) n bSmall := by
    simp_all +decide [ smallChainComplex_d ];
    exact Subtype.ext hbChain_eq.symm;
  -- Apply `homologyπ_zero_of_iCycles_eq_d` to conclude that `(S.homologyπ n).hom w = 0`.
  have h_zero : (smallChainComplex R X 𝒰).homologyπ n w = 0 := by
    apply homologyπ_zero_of_iCycles_eq_d;
    exact h_eq;
  exact eq_of_sub_eq_zero ( hw.symm.trans h_zero )

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
