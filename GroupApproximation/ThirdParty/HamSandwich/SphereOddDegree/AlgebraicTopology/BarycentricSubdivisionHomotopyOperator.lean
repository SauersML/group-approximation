import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionCone
import Mathlib

/-!
# The recursive homotopy operator between identity and barycentric subdivision

This file defines the classical recursive chain-homotopy operator `H` between the
identity and the barycentric subdivision chain map.  Only the **definition** and
its basic naturality / pushforward API are provided here; the chain-homotopy
identity `∂H + H∂ = id - sd` is proved in a later file.

## Construction

For the standard `n`-simplex we define a chain `T_n` of degree `+1` recursively
by coning from the barycenter `b_n`:

```text
T_n(ι_n) = Cone_{b_n}(ι_n - sd(ι_n) - H(∂ι_n))
```

where `ι_n` is the identity singular `n`-simplex of `Δⁿ`, `sd(ι_n)` is its
barycentric subdivision, and `H(∂ι_n)` applies the (lower-degree) homotopy
operator to the boundary of `ι_n`.  The homotopy operator on a general space `X`
is obtained from `T_n` by pushforward:

```text
H_X(σ) = σ_#(T_n(ι_n)),
```

extended linearly.

## Main definitions

* `singularChainMap` — the functorial pushforward of singular chains along a
  continuous map (a degree-wise component of the singular chain complex functor).
* `deltaBarycenter` — the barycenter of `Δⁿ`.
* `stdSimplexIdSingularSimplex` — the identity singular `n`-simplex of `Δⁿ`.
* `barycentricHomotopyUniversal` — the universal chain `T_n(ι_n)`.
* `barycentricSubdivisionHomotopyLinearMap` — the degree `+1` homotopy operator
  on singular chains of an arbitrary space, with generator formula
  `barycentricSubdivisionHomotopyLinearMap_apply_generator`.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 1. Pushforward of singular chains along a continuous map -/

/-- **Pushforward of singular chains.** The degree-`n` component of the chain map
induced by a continuous map `f : X ⟶ Y` via the singular chain complex functor. -/
noncomputable def singularChainMap (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R Y n :=
  (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f n

/-- The pushforward of a singular simplex `σ` along `f`, at the level of
singular simplices. -/
noncomputable def pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (σ : singularSimplices X n) : singularSimplices Y n :=
  (TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ

/-- **Pushforward on a generator.** `singularChainMap` sends the basis chain of a
simplex `σ` to the basis chain of its pushforward `pushSimplex f n σ`. -/
theorem singularChainMap_generator (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n) :
    (singularChainMap R f n).hom (chainGenerator R X n σ)
      = chainGenerator R Y n (pushSimplex f n σ) := by
  unfold singularChainMap chainGenerator pushSimplex
  have key : (Limits.Sigma.ι (fun (_ : singularSimplices X n) => ModuleCat.of R R) σ)
      ≫ (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f).f n
      = Limits.Sigma.ι (fun (_ : singularSimplices Y n) => ModuleCat.of R R)
        ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n)) σ) := by
    simp [singularChainComplexFunctor, SSet.singularChainComplexFunctor,
      SimplicialObject.whiskering, Limits.sigmaConst]
  have := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom key) (1 : R)
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this

/-- **Naturality of the boundary.** The pushforward is a chain map, so it commutes
with the singular boundary:
`∂ ∘ f_# = f_# ∘ ∂`. -/
theorem singularChainMap_boundary (R : Type) [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    singularChainMap R f (n + 1) ≫ singularBoundary R Y n
      = singularBoundary R X n ≫ singularChainMap R f n := by
  have h := ((((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map f)).comm (n + 1) n
  simp [singularChainMap, singularBoundary, h]

/-! ## 2. The barycenter and the identity singular simplex of `Δⁿ` -/

/-- The barycenter of the standard `n`-simplex `Δⁿ`. -/
noncomputable def deltaBarycenter (n : ℕ) : Delta n :=
  stdSimplex.barycenter (X := Fin (n + 1)) (𝕜 := ℝ)

/-- The identity singular `n`-simplex `ι_n` of `Δⁿ`, i.e. the singular simplex
corresponding to the identity continuous map of `Δⁿ`. -/
noncomputable def stdSimplexIdSingularSimplex (n : ℕ) :
    singularSimplices (TopCat.of (Delta n)) n :=
  continuousMapAsSingularSimplex (TopCat.of (Delta n)) n (ContinuousMap.id (Delta n))

/-! ## 3. The homotopy operator built from a universal chain -/

/-- The `R`-linear map `R → C_{n+1}(X; R)` sending `1` to the pushforward of a
universal degree-`(n+1)` chain `T` along the singular simplex `σ`. -/
noncomputable def pushUniversalHom (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1))
    (σ : singularSimplices X n) :
    ModuleCat.of R R ⟶ singularChainGroup R X (n + 1) :=
  ModuleCat.ofHom
    { toFun := fun r =>
        r • (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom T
      map_add' := by intro r s; simp [add_smul]
      map_smul' := by intro a r; simp [mul_smul] }

/-- The degree-`n` homotopy operator on singular chains of `X` determined by a
universal chain `T` on `Δⁿ`: it pushes `T` forward along each singular simplex
and extends linearly. -/
noncomputable def homotopyFromUniversal (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1)) :
    singularChainGroup R X n ⟶ singularChainGroup R X (n + 1) :=
  Sigma.desc (pushUniversalHom R X n T)

/-- The homotopy operator built from `T` has the prescribed value on a basis
generator: the pushforward of `T` along `σ`. -/
theorem homotopyFromUniversal_generator (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (T : singularChainGroup R (TopCat.of (Delta n)) (n + 1))
    (σ : singularSimplices X n) :
    (homotopyFromUniversal R X n T).hom (chainGenerator R X n σ)
      = (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom T := by
  convert one_smul _ _
  convert congr_arg
    (fun f : ModuleCat.of R R ⟶ singularChainGroup R X (n + 1) => f.hom 1)
    (Sigma.ι_desc (fun σ => pushUniversalHom R X n T σ) σ) using 1

/-! ## 4. The universal homotopy chain `T_n(ι_n)` -/

/-- **The universal homotopy chain** `T_n(ι_n) : C_{n+1}(Δⁿ; R)`, defined
recursively by coning from the barycenter:

```text
T_n = Cone_{b_n}(ι_n - sd(ι_n) - H(∂ι_n)),
```

where the term `H(∂ι_n)` (present only for `n ≥ 1`) applies the homotopy operator
built from the previous universal chain `T_{n-1}` to the boundary of `ι_n`. -/
noncomputable def barycentricHomotopyUniversal (R : Type) [CommRing R] :
    (n : ℕ) → singularChainGroup R (TopCat.of (Delta n)) (n + 1)
  | 0 =>
      (coneLinearMap R 0 0 (deltaBarycenter 0)).hom
        (chainGenerator R (TopCat.of (Delta 0)) 0 (stdSimplexIdSingularSimplex 0)
          - (barycentricSubdivisionLinearMap R (TopCat.of (Delta 0)) 0).hom
              (chainGenerator R (TopCat.of (Delta 0)) 0 (stdSimplexIdSingularSimplex 0)))
  | (m + 1) =>
      (coneLinearMap R (m + 1) (m + 1) (deltaBarycenter (m + 1))).hom
        (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1) (stdSimplexIdSingularSimplex (m + 1))
          - (barycentricSubdivisionLinearMap R (TopCat.of (Delta (m + 1))) (m + 1)).hom
              (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                (stdSimplexIdSingularSimplex (m + 1)))
          - (homotopyFromUniversal R (TopCat.of (Delta (m + 1))) m
                (barycentricHomotopyUniversal R m)).hom
              ((singularBoundary R (TopCat.of (Delta (m + 1))) m).hom
                (chainGenerator R (TopCat.of (Delta (m + 1))) (m + 1)
                  (stdSimplexIdSingularSimplex (m + 1)))))

/-! ## 5. The degree-wise homotopy operator -/

/-- **The barycentric subdivision homotopy operator** `H : C_n(X; R) → C_{n+1}(X; R)`,
obtained by pushing the universal chain `T_n` forward along each singular simplex
and extending linearly. -/
noncomputable def barycentricSubdivisionHomotopyLinearMap (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    singularChainGroup R X n ⟶ singularChainGroup R X (n + 1) :=
  homotopyFromUniversal R X n (barycentricHomotopyUniversal R n)

/-- **Generator formula.** On a singular simplex `σ`, the homotopy operator is the
pushforward of the universal chain `T_n` along `σ`. -/
theorem barycentricSubdivisionHomotopyLinearMap_apply_generator (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (chainGenerator R X n σ)
      = (singularChainMap R (TopCat.ofHom (singularSimplexAsContinuousMap X n σ)) (n + 1)).hom
          (barycentricHomotopyUniversal R n) := by
  rw [barycentricSubdivisionHomotopyLinearMap, homotopyFromUniversal_generator]

/-- The homotopy operator sends `0` to `0`. -/
theorem barycentricSubdivisionHomotopyLinearMap_map_zero (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom 0 = 0 :=
  map_zero _

/-- The homotopy operator is additive. -/
theorem barycentricSubdivisionHomotopyLinearMap_map_add (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (c d : singularChainGroup R X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (c + d)
      = (barycentricSubdivisionHomotopyLinearMap R X n).hom c
        + (barycentricSubdivisionHomotopyLinearMap R X n).hom d :=
  map_add _ c d

/-- The homotopy operator is `R`-linear in the scalar action. -/
theorem barycentricSubdivisionHomotopyLinearMap_smul (R : Type) [CommRing R]
    (X : TopCat.{0}) (n : ℕ) (a : R) (c : singularChainGroup R X n) :
    (barycentricSubdivisionHomotopyLinearMap R X n).hom (a • c)
      = a • (barycentricSubdivisionHomotopyLinearMap R X n).hom c :=
  map_smul _ a c

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
