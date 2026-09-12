import GroupApproximation.CharClass.CohomologyBasic
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.SingularCohomologyHomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UnitInterval

/-!
# Bridging concrete spaces into `TopCat.{0}`, and homotopy invariance

The LIX program's spaces are concrete `Type`s: subtypes of `Fin n → ℂ` and of
`EuclideanSpace ℝ (Fin k)`, matrices, and finite products of these.  This file
supplies the plumbing that turns such a `Type` and its continuous maps into
objects and morphisms of `TopCat.{0}`, and the homotopy-invariance consequences
that make cohomology computable: a homotopy equivalence induces a linear
isomorphism on `H^*`, so in particular

```text
H^*(X × [0,1]; F₂) ≅ H^*(X; F₂)     and     H^*(X × ℝ^k; F₂) ≅ H^*(X; F₂),
```

both realized by the pullback along the first projection.

## Main declarations

* `cmap f` — a `C(X, Y)` as a `TopCat` morphism; `pullMap f n` its pullback.
* `pull_eq_of_homotopic`, `pull_eq_of_homotopy` — homotopy invariance.
* `pullEquivOfHomotopyEquiv`, `pullEquivOfHomeomorph` — the induced linear
  isomorphisms on `H^n`.
* `inclSubtype`, `restrictTo` — restriction of a class to a subspace (in
  particular to an open subset), with `restrictTo_cup` and `restrictTo_one`.
* `fstMap`, `sndMap`, `prodMap` — the product bridging.
* `prodContractibleEquiv`, `cohProdContractible` — `X × C ≃ X` for contractible
  `C`, and the resulting isomorphism on `H^n`, which **is** `pr₁^*`.
* `cohProdUnitInterval`, `cohProdEuclidean` — the two named special cases.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. Concrete spaces and maps as `TopCat` data -/

/-- A continuous map between concrete spaces, as a morphism of `TopCat.{0}`. -/
abbrev cmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    TopCat.of X ⟶ TopCat.of Y :=
  TopCat.ofHom f

/-- The pullback along a continuous map of concrete spaces. -/
def pullMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a : Hmod2 (TopCat.of Y) n) : Hmod2 (TopCat.of X) n :=
  pull (cmap f) n a

theorem pullMap_eq {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a : Hmod2 (TopCat.of Y) n) : pullMap f n a = pull (cmap f) n a := rfl

@[simp] theorem pullMap_id {X : Type} [TopologicalSpace X] (n : ℕ)
    (a : Hmod2 (TopCat.of X) n) : pullMap (ContinuousMap.id X) n a = a :=
  pull_id n a

theorem pullMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (a : Hmod2 (TopCat.of Z) n) :
    pullMap (g.comp f) n a = pullMap f n (pullMap g n a) :=
  pull_comp (cmap f) (cmap g) n a

theorem pullMap_cup {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {p q : ℕ} (a : Hmod2 (TopCat.of Y) p) (b : Hmod2 (TopCat.of Y) q) :
    pullMap f (p + q) (cup a b) = cup (pullMap f p a) (pullMap f q b) :=
  pull_cup (cmap f) a b

@[simp] theorem pullMap_one {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : pullMap f 0 (one (TopCat.of Y)) = one (TopCat.of X) :=
  pull_one (cmap f)

/-! ## 2. Homotopy invariance -/

/-- **Homotopy invariance.**  Homotopic maps have equal pullbacks. -/
theorem pull_eq_of_homotopic {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) (a : Hmod2 Y n) :
    pull f n a = pull g n a := by
  have hm := singularCohomologyZMod2_map_eq_of_homotopic n h
  show ((singularCohomologyZMod2 n).map f.op).hom a = ((singularCohomologyZMod2 n).map g.op).hom a
  rw [hm]

/-- **Homotopy invariance**, from a homotopy rather than the `Homotopic` relation. -/
theorem pull_eq_of_homotopy {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) (a : Hmod2 Y n) :
    pull f n a = pull g n a :=
  pull_eq_of_homotopic ⟨H⟩ n a

/-- **Homotopy invariance** for maps of concrete spaces. -/
theorem pullMap_eq_of_homotopic {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : ContinuousMap.Homotopic f g) (n : ℕ) (a : Hmod2 (TopCat.of Y) n) :
    pullMap f n a = pullMap g n a :=
  pull_eq_of_homotopic (f := cmap f) (g := cmap g) h n a

/-- A homotopy equivalence induces a linear isomorphism on `H^n`, given by the
pullback along it. -/
def pullEquivOfHomotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Hmod2 (TopCat.of Y) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of X) n :=
  LinearEquiv.ofLinear (pullLinear (cmap e.toFun) n) (pullLinear (cmap e.invFun) n)
    (by
      ext b
      show pull (cmap e.toFun) n (pull (cmap e.invFun) n b) = b
      rw [← pull_comp,
        show (cmap e.toFun ≫ cmap e.invFun) = cmap (e.invFun.comp e.toFun) from rfl,
        pull_eq_of_homotopic (f := cmap (e.invFun.comp e.toFun)) (g := 𝟙 (TopCat.of X))
          e.left_inv n b, pull_id])
    (by
      ext a
      show pull (cmap e.invFun) n (pull (cmap e.toFun) n a) = a
      rw [← pull_comp,
        show (cmap e.invFun ≫ cmap e.toFun) = cmap (e.toFun.comp e.invFun) from rfl,
        pull_eq_of_homotopic (f := cmap (e.toFun.comp e.invFun)) (g := 𝟙 (TopCat.of Y))
          e.right_inv n a, pull_id])

@[simp] theorem pullEquivOfHomotopyEquiv_apply {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ)
    (a : Hmod2 (TopCat.of Y) n) :
    pullEquivOfHomotopyEquiv e n a = pullMap e.toFun n a := rfl

/-- A homeomorphism induces a linear isomorphism on `H^n`. -/
def pullEquivOfHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) : Hmod2 (TopCat.of Y) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of X) n :=
  pullEquivOfHomotopyEquiv e.toHomotopyEquiv n

/-- A `TopCat` isomorphism induces a linear isomorphism on `H^n`. -/
def pullEquivOfIso {X Y : TopCat.{0}} (e : X ≅ Y) (n : ℕ) :
    Hmod2 Y n ≃ₗ[ZMod 2] Hmod2 X n :=
  LinearEquiv.ofLinear (pullLinear e.hom n) (pullLinear e.inv n)
    (by
      ext b
      show pull e.hom n (pull e.inv n b) = b
      rw [← pull_comp, e.hom_inv_id, pull_id])
    (by
      ext a
      show pull e.inv n (pull e.hom n a) = a
      rw [← pull_comp, e.inv_hom_id, pull_id])

/-! ## 3. Subspaces -/

/-- The inclusion of a subspace, as a `TopCat` morphism. -/
def inclSubtype {X : Type} [TopologicalSpace X] (S : Set X) : TopCat.of S ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Restriction of a cohomology class to a subspace (in particular, to an open
subset). -/
def restrictTo {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ)
    (a : Hmod2 (TopCat.of X) n) : Hmod2 (TopCat.of S) n :=
  pull (inclSubtype S) n a

@[simp] theorem restrictTo_add {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ)
    (a b : Hmod2 (TopCat.of X) n) :
    restrictTo S n (a + b) = restrictTo S n a + restrictTo S n b :=
  pull_add _ n a b

@[simp] theorem restrictTo_zero {X : Type} [TopologicalSpace X] (S : Set X) (n : ℕ) :
    restrictTo S n (0 : Hmod2 (TopCat.of X) n) = 0 :=
  pull_zero _ n

theorem restrictTo_cup {X : Type} [TopologicalSpace X] (S : Set X) {p q : ℕ}
    (a : Hmod2 (TopCat.of X) p) (b : Hmod2 (TopCat.of X) q) :
    restrictTo S (p + q) (cup a b) = cup (restrictTo S p a) (restrictTo S q b) :=
  pull_cup (inclSubtype S) a b

@[simp] theorem restrictTo_one {X : Type} [TopologicalSpace X] (S : Set X) :
    restrictTo S 0 (one (TopCat.of X)) = one (TopCat.of S) :=
  pull_one (inclSubtype S)

/-! ## 4. Products -/

/-- The first projection of a product, as a `TopCat` morphism. -/
abbrev fstMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    TopCat.of (X × Y) ⟶ TopCat.of X :=
  cmap ContinuousMap.fst

/-- The second projection of a product, as a `TopCat` morphism. -/
abbrev sndMap (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    TopCat.of (X × Y) ⟶ TopCat.of Y :=
  cmap ContinuousMap.snd

/-- A product of continuous maps, as a `TopCat` morphism. -/
abbrev prodMap {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y')) :
    TopCat.of (X × Y) ⟶ TopCat.of (X' × Y') :=
  cmap (f.prodMap g)

/-! ## 5. Contractible factors -/

/-- The unit interval is contractible (it is a nonempty convex subset of `ℝ`). -/
instance contractibleSpace_unitInterval : ContractibleSpace unitInterval :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩

/-- Projection is a homotopy equivalence off a contractible factor. -/
def prodContractibleEquiv (X C : Type) [TopologicalSpace X] [TopologicalSpace C]
    [ContractibleSpace C] : ContinuousMap.HomotopyEquiv (X × C) X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (ContractibleSpace.hequiv_unit C).some).trans
    (Homeomorph.prodPUnit X).toHomotopyEquiv

/-- The homotopy equivalence `X × C ≃ X` of `prodContractibleEquiv` **is** the
first projection; so the induced isomorphism on `H^*` is `pr₁^*`. -/
theorem prodContractibleEquiv_toFun (X C : Type) [TopologicalSpace X] [TopologicalSpace C]
    [ContractibleSpace C] :
    (prodContractibleEquiv X C).toFun = (ContinuousMap.fst : C(X × C, X)) := by
  ext x
  rfl

/-- **`H^n(X × C) ≅ H^n(X)` for contractible `C`**, realized by `pr₁^*`. -/
def cohProdContractible (X C : Type) [TopologicalSpace X] [TopologicalSpace C]
    [ContractibleSpace C] (n : ℕ) :
    Hmod2 (TopCat.of X) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of (X × C)) n :=
  pullEquivOfHomotopyEquiv (prodContractibleEquiv X C) n

theorem cohProdContractible_apply (X C : Type) [TopologicalSpace X] [TopologicalSpace C]
    [ContractibleSpace C] (n : ℕ) (a : Hmod2 (TopCat.of X) n) :
    cohProdContractible X C n a = pull (fstMap X C) n a := by
  show pullMap (prodContractibleEquiv X C).toFun n a = _
  rw [prodContractibleEquiv_toFun]
  rfl

/-- **`H^n(X × [0,1]) ≅ H^n(X)`.** -/
def cohProdUnitInterval (X : Type) [TopologicalSpace X] (n : ℕ) :
    Hmod2 (TopCat.of X) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of (X × unitInterval)) n :=
  cohProdContractible X unitInterval n

/-- **`H^n(X × ℝ^k) ≅ H^n(X)`.** -/
def cohProdEuclidean (X : Type) [TopologicalSpace X] (k n : ℕ) :
    Hmod2 (TopCat.of X) n ≃ₗ[ZMod 2] Hmod2 (TopCat.of (X × EuclideanSpace ℝ (Fin k))) n :=
  cohProdContractible X (EuclideanSpace ℝ (Fin k)) n

end

end GroupApproximation.CharClass
