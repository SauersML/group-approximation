import GroupApproximation.CharClass.CartanTargetEquivariance
import GroupApproximation.CharClass.CartanSourceBoundary
import GroupApproximation.CharClass.SteenrodDiagonalPhi

/-!
# `X ↦ S(X) ⊗ S(X)` is functorial, equivariantly and over the pair differential

The acyclic-models comparison needs the target of Steenrod's diagonal as a
*functor* into complexes of `Λ`-modules.  This file supplies the morphism half:
a continuous map pushes a pair of singular simplices forward, and that operation

* is functorial (`pairIdxMap_id`, `pairIdxMap_comp`),
* commutes with the factor swap, hence is `Λ`-linear (`pairMapLambda`),
* commutes with `cc-steenrod`'s pair differential (`dTgt_pairMap`).

Everything rests on one naturality statement about faces, `pushSimplex_faceSimplex`,
and that one is `rfl` after passing to the bare hom-set model of
`CartanSourceBoundary.lean`: a face is precomposition with a coface, a pushforward
is postcomposition, and the two commute by associativity.

The file also fixes the name collision with `cc-steenrod`.  Their `swapIdx`,
`swapEnd` and `tgtModule` and this lane's `pairIdxSwap`, `pairSwap` and
`pairModule` are the same objects; theirs are canonical because `tgtModule` is a
global instance, and the bridges here are all `rfl`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 0. Bridges to `cc-steenrod`'s names -/

theorem swapEnd_eq_pairSwap (X : TopCat.{0}) (k : ℕ) :
    Steenrod.swapEnd X k = pairSwap X k := rfl

/-- The differential commutes with the swap, in `cc-steenrod`'s vocabulary. -/
theorem dTgt_swapEnd (X : TopCat.{0}) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    Steenrod.dTgt X (ZMod 2) k (Steenrod.swapEnd X (k + 1) y)
      = Steenrod.swapEnd X k (Steenrod.dTgt X (ZMod 2) k y) :=
  dTgt_pairSwap X k y

/-- **The differential is `Λ`-linear** for the global instance `Steenrod.tgtModule`. -/
theorem dTgt_smul_tgtModule (X : TopCat.{0}) (k : ℕ) (c : GroupRingZ2)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    Steenrod.dTgt X (ZMod 2) k (c • y) = c • Steenrod.dTgt X (ZMod 2) k y :=
  galAlgHom_comm (Steenrod.swapEnd X (k + 1)) (Steenrod.swapEnd_sq X (k + 1))
    (Steenrod.swapEnd X k) (Steenrod.swapEnd_sq X k) (Steenrod.dTgt X (ZMod 2) k)
    (dTgt_swapEnd X k) c y

/-! ## 1. Pushforward of simplices, functorially -/

theorem pushSimplex_id (X : TopCat.{0}) (n : ℕ) (σ : singularSimplices X n) :
    pushSimplex (𝟙 X) n σ = σ := by
  apply (simplexEquiv X n).injective
  rw [simplexEquiv_pushSimplex, Category.comp_id]

theorem pushSimplex_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (σ : singularSimplices X n) :
    pushSimplex (f ≫ g) n σ = pushSimplex g n (pushSimplex f n σ) := by
  apply (simplexEquiv Z n).injective
  rw [simplexEquiv_pushSimplex, simplexEquiv_pushSimplex, simplexEquiv_pushSimplex,
    Category.assoc]

/-- **Faces are natural.**  A face is precomposition with a coface and a
pushforward is postcomposition, so the two commute by associativity. -/
theorem pushSimplex_faceSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (i : Fin (n + 2)) (σ : singularSimplices X (n + 1)) :
    pushSimplex f n (faceSimplex X n i σ)
      = faceSimplex Y n i (pushSimplex f (n + 1) σ) := by
  apply (simplexEquiv Y n).injective
  rw [simplexEquiv_pushSimplex, simplexEquiv_faceSimplex, simplexEquiv_faceSimplex,
    simplexEquiv_pushSimplex]
  exact Category.assoc _ _ _

/-! ## 2. The functorial map on pairs -/

/-- Push both members of a pair forward; the two degrees are untouched. -/
def pairIdxMap {X Y : TopCat.{0}} (f : X ⟶ Y) {k : ℕ}
    (q : Steenrod.PairIdx X k) : Steenrod.PairIdx Y k :=
  ⟨q.1, (pushSimplex f q.1.val.1 q.2.1, pushSimplex f q.1.val.2 q.2.2)⟩

theorem pairIdxMap_id {X : TopCat.{0}} {k : ℕ} (q : Steenrod.PairIdx X k) :
    pairIdxMap (𝟙 X) q = q := by
  obtain ⟨p, σ, τ⟩ := q
  rw [pairIdxMap, pushSimplex_id, pushSimplex_id]

theorem pairIdxMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {k : ℕ}
    (q : Steenrod.PairIdx X k) :
    pairIdxMap (f ≫ g) q = pairIdxMap g (pairIdxMap f q) := by
  obtain ⟨p, σ, τ⟩ := q
  rw [pairIdxMap, pairIdxMap, pairIdxMap, pushSimplex_comp, pushSimplex_comp]

/-- Pushing forward commutes with the factor swap, on the index. -/
theorem pairIdxMap_swapIdx {X Y : TopCat.{0}} (f : X ⟶ Y) {k : ℕ}
    (q : Steenrod.PairIdx X k) :
    pairIdxMap f (Steenrod.swapIdx q) = Steenrod.swapIdx (pairIdxMap f q) := rfl

/-- The pushforward on chains, `F₂`-linearly. -/
def pairMapF2 {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    (Steenrod.PairIdx X k →₀ ZMod 2) →ₗ[ZMod 2] (Steenrod.PairIdx Y k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pairIdxMap f)

@[simp] theorem pairMapF2_single {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (q : Steenrod.PairIdx X k) (c : ZMod 2) :
    pairMapF2 f k (Finsupp.single q c) = Finsupp.single (pairIdxMap f q) c := by
  unfold pairMapF2
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem pairMapF2_swapEnd {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    pairMapF2 f k (Steenrod.swapEnd X k y)
      = Steenrod.swapEnd Y k (pairMapF2 f k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single q c => rw [Steenrod.swapEnd_single, pairMapF2_single, pairMapF2_single,
      Steenrod.swapEnd_single, pairIdxMap_swapIdx]

/-- **The pushforward is `Λ`-linear**, because it commutes with the swap. -/
def pairMapLambda {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    (Steenrod.PairIdx X k →₀ ZMod 2) →ₗ[GroupRingZ2] (Steenrod.PairIdx Y k →₀ ZMod 2) where
  toFun := pairMapF2 f k
  map_add' u v := map_add _ u v
  map_smul' c y :=
    galAlgHom_comm (Steenrod.swapEnd X k) (Steenrod.swapEnd_sq X k)
      (Steenrod.swapEnd Y k) (Steenrod.swapEnd_sq Y k) (pairMapF2 f k)
      (pairMapF2_swapEnd f k) c y

@[simp] theorem pairMapLambda_single {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (q : Steenrod.PairIdx X k) (c : ZMod 2) :
    pairMapLambda f k (Finsupp.single q c) = Finsupp.single (pairIdxMap f q) c :=
  pairMapF2_single f k q c

/-! ## 3. The pushforward is a chain map -/

/-- The pushforward of a single left-face basis pair, with the face already moved
across.  Stated with the index written out, so that it can be used by `exact`:
`PairDeg` is a `def`, and a `rw` against a statement that names `PairIdx`
explicitly fails the motive check at `instances` transparency. -/
theorem pairMapF2_single_dLeft {X Y : TopCat.{0}} (f : X ⟶ Y) (k a' b : ℕ)
    (hab : a' + b = k) (j : Fin (a' + 2))
    (σ : singularSimplices X (a' + 1)) (τ : singularSimplices X b) :
    pairMapF2 f k (Finsupp.single (⟨⟨(a', b), hab⟩, (faceSimplex X a' j σ, τ)⟩ :
        Steenrod.PairIdx X k) 1)
      = Finsupp.single (⟨⟨(a', b), hab⟩,
          (faceSimplex Y a' j (pushSimplex f (a' + 1) σ), pushSimplex f b τ)⟩ :
        Steenrod.PairIdx Y k) 1 := by
  rw [pairMapF2_single]
  exact congrArg (fun ρ => Finsupp.single
    (⟨⟨(a', b), hab⟩, (ρ, pushSimplex f b τ)⟩ : Steenrod.PairIdx Y k) (1 : ZMod 2))
    (pushSimplex_faceSimplex f a' j σ)

/-- The same on the right factor. -/
theorem pairMapF2_single_dRight {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b' : ℕ)
    (hab : a + b' = k) (j : Fin (b' + 2))
    (σ : singularSimplices X a) (τ : singularSimplices X (b' + 1)) :
    pairMapF2 f k (Finsupp.single (⟨⟨(a, b'), hab⟩, (σ, faceSimplex X b' j τ)⟩ :
        Steenrod.PairIdx X k) 1)
      = Finsupp.single (⟨⟨(a, b'), hab⟩,
          (pushSimplex f a σ, faceSimplex Y b' j (pushSimplex f (b' + 1) τ))⟩ :
        Steenrod.PairIdx Y k) 1 := by
  rw [pairMapF2_single]
  exact congrArg (fun ρ => Finsupp.single
    (⟨⟨(a, b'), hab⟩, (pushSimplex f a σ, ρ)⟩ : Steenrod.PairIdx Y k) (1 : ZMod 2))
    (pushSimplex_faceSimplex f b' j τ)

theorem dLeft_pairIdxMap {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ)
    (h : a + b = k + 1) (σ : singularSimplices X a) (τ : singularSimplices X b) :
    Steenrod.dLeft Y (ZMod 2) k a b h (pushSimplex f a σ) (pushSimplex f b τ)
      = pairMapF2 f k (Steenrod.dLeft X (ZMod 2) k a b h σ τ) := by
  cases a with
  | zero => rw [Steenrod.dLeft_zero, Steenrod.dLeft_zero, map_zero]
  | succ a' =>
      rw [Steenrod.dLeft_succ, Steenrod.dLeft_succ]
      refine Eq.trans ?_ (map_sum (pairMapF2 f k) _ Finset.univ).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (pairMapF2_single_dLeft f k a' b _ j σ τ).symm

theorem dRight_pairIdxMap {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ)
    (h : a + b = k + 1) (σ : singularSimplices X a) (τ : singularSimplices X b) :
    Steenrod.dRight Y (ZMod 2) k a b h (pushSimplex f a σ) (pushSimplex f b τ)
      = pairMapF2 f k (Steenrod.dRight X (ZMod 2) k a b h σ τ) := by
  cases b with
  | zero => rw [Steenrod.dRight_zero, Steenrod.dRight_zero, map_zero]
  | succ b' =>
      rw [Steenrod.dRight_succ, Steenrod.dRight_succ]
      refine Eq.trans ?_ (map_sum (pairMapF2 f k) _ Finset.univ).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      exact (pairMapF2_single_dRight f k a b' _ j σ τ).symm

theorem dGen_pairIdxMap {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (q : Steenrod.PairIdx X (k + 1)) :
    Steenrod.dGen Y (ZMod 2) k (pairIdxMap f q)
      = pairMapF2 f k (Steenrod.dGen X (ZMod 2) k q) := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, σ, τ⟩ := q
  have key : Steenrod.dLeft Y (ZMod 2) k a b hab (pushSimplex f a σ) (pushSimplex f b τ)
        + Steenrod.dRight Y (ZMod 2) k a b hab (pushSimplex f a σ) (pushSimplex f b τ)
      = pairMapF2 f k (Steenrod.dLeft X (ZMod 2) k a b hab σ τ
          + Steenrod.dRight X (ZMod 2) k a b hab σ τ) := by
    rw [dLeft_pairIdxMap f k a b hab σ τ, dRight_pairIdxMap f k a b hab σ τ, map_add]
  exact key

/-- **The pushforward is a chain map** for `cc-steenrod`'s pair differential. -/
theorem dTgt_pairMap {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (y : Steenrod.PairIdx X (k + 1) →₀ ZMod 2) :
    Steenrod.dTgt Y (ZMod 2) k (pairMapF2 f (k + 1) y)
      = pairMapF2 f k (Steenrod.dTgt X (ZMod 2) k y) := by
  induction y using Finsupp.induction_linear with
  | zero => rfl
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single q c =>
      rw [pairMapF2_single, Steenrod.dTgt_single, Steenrod.dTgt_single, map_smul,
        dGen_pairIdxMap]

end

end GroupApproximation.CharClass
