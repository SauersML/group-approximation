import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SubordinateChains
import Mathlib

/-!
# Coordinate "keep" projections on singular chains

The singular chain group `C_n(X; R)` is the free `R`-module on the singular
`n`-simplices.  For any predicate `P` on simplices, the **coordinate projection**
`keepHom P` keeps the basis chains of simplices satisfying `P` and zeroes out the
rest:

```text
keepHom P (chainGenerator σ) = if P σ then chainGenerator σ else 0.
```

These projections are the algebraic device used to *split* a singular chain by
the open set its simplices belong to, the key ingredient in the degreewise
splitting of the singular Mayer–Vietoris short exact sequence.
-/

open CategoryTheory AlgebraicTopology Limits
open AffineBarycentricSubdivision

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree


variable {R : Type} [CommRing R] {X : TopCat.{0}}

/-- The coordinate projection on `C_n(X; R)` that keeps exactly the basis chains
of simplices satisfying `P`. -/
noncomputable def keepHom (R : Type) [CommRing R] (X : TopCat.{0}) {n : ℕ}
    (P : singularSimplices X n → Prop) [DecidablePred P] :
    singularChainGroup R X n ⟶ singularChainGroup R X n :=
  Sigma.desc fun σ =>
    if P σ then Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ else 0

/-- The value of the coordinate projection on a basis chain. -/
theorem keepHom_generator {n : ℕ} (P : singularSimplices X n → Prop) [DecidablePred P]
    (σ : singularSimplices X n) :
    (keepHom R X P).hom (chainGenerator R X n σ)
      = if P σ then chainGenerator R X n σ else 0 := by
  have h : Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ
        ≫ keepHom R X P
      = if P σ then Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ else 0 :=
    Sigma.ι_desc _ _
  have h2 := congrArg
    (fun f : ModuleCat.of R R ⟶ singularChainGroup R X n => f.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  refine h2.trans ?_
  by_cases hP : P σ
  · rw [if_pos hP, if_pos hP]; rfl
  · rw [if_neg hP, if_neg hP]; simp

/-- **Support of a kept chain.** If `c` is subordinate to `T` and we keep the
simplices subordinate to `S`, the result is subordinate to `S ∩ T`. -/
theorem keepHom_mem_subChainSubmodule {n : ℕ} {S T : Set X}
    [DecidablePred (IsSubordinate (X := X) S (n := n))]
    {c : singularChainGroup R X n} (hc : c ∈ subChainSubmodule R X T n) :
    (keepHom R X (IsSubordinate S)).hom c ∈ subChainSubmodule R X (S ∩ T) n := by
  refine subChainSubmodule_induction (S := T)
    (p := fun x => (keepHom R X (IsSubordinate S)).hom x ∈ subChainSubmodule R X (S ∩ T) n)
    ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [keepHom_generator]
    by_cases hS : IsSubordinate S σ
    · rw [if_pos hS]
      exact chainGenerator_mem_subChainSubmodule (Set.subset_inter hS hσ)
    · rw [if_neg hS]
      exact Submodule.zero_mem _
  · show (keepHom R X (IsSubordinate S)).hom 0 ∈ _
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    show (keepHom R X (IsSubordinate S)).hom (x + y) ∈ _
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x hx
    show (keepHom R X (IsSubordinate S)).hom (a • x) ∈ _
    rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- A chain subordinate to `S` is fixed by keeping the `S`-subordinate
simplices. -/
theorem keepHom_eq_self_of_mem {n : ℕ} {S : Set X}
    [DecidablePred (IsSubordinate (X := X) S (n := n))]
    {c : singularChainGroup R X n} (hc : c ∈ subChainSubmodule R X S n) :
    (keepHom R X (IsSubordinate S)).hom c = c := by
  refine subChainSubmodule_induction (S := S)
    (p := fun x => (keepHom R X (IsSubordinate S)).hom x = x) ?_ ?_ ?_ ?_ hc
  · intro σ hσ
    rw [keepHom_generator, if_pos hσ]
  · show (keepHom R X (IsSubordinate S)).hom 0 = 0
    rw [map_zero]
  · intro x y hx hy
    show (keepHom R X (IsSubordinate S)).hom (x + y) = x + y
    rw [map_add, hx, hy]
  · intro a x hx
    show (keepHom R X (IsSubordinate S)).hom (a • x) = a • x
    rw [map_smul, hx]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
