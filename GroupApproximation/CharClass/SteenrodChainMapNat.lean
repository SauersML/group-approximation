import GroupApproximation.CharClass.SteenrodChainMapHom
import GroupApproximation.CharClass.CartanSourceFunctor

/-!
# Naturality of the diagonal, and of the target

`Φ` has to be a *natural* transformation for the acyclic-models comparison to
apply to it, and the target has to be a functor for there to be a natural
transformation into.  Both come from one observation: pushing a pair of simplices
forward along a map of spaces commutes with everything in sight — with the factor
swap, because it acts on the two factors separately; with each half of the pair
differential, because it commutes with face maps; and with the cut diagonal,
because a face of a pushed-forward simplex is the pushforward of the face.

The last of those is already `steenrodDiag_naturality`, so the work here is
transport rather than combinatorics.

## Contents

* `pairIdxPush`, `pairPushLin` — the pushforward on the target, and its
  `Λ`-linearity, which the target needs to be a functor into `Λ`-modules at all.
* `smul_of_swap` — the criterion: an `F₂`-linear map between two of these modules
  commuting with the swaps is `Λ`-linear.  Stated once and used twice.
* `dTgt_naturality` — the target differential is natural.
* `PhiHom_naturality` — **`Φ` is natural**, against `cc-cartan`'s `srcMapIdx`.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The pushforward on the target -/

/-- Pushing a pair index forward along a map of spaces: the bidegree is
untouched, both simplices move. -/
def pairIdxPush {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (q : PairIdx X k) : PairIdx Y k :=
  ⟨q.1, (pushSimplex f q.1.val.1 q.2.1, pushSimplex f q.1.val.2 q.2.2)⟩

/-- The pushforward on the target module, `F₂`-linearly. -/
def pairPushLin (X Y : TopCat.{0}) (f : X ⟶ Y) (k : ℕ) :
    (PairIdx X k →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx Y k →₀ ZMod 2) :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pairIdxPush f k)

theorem pairPushLin_single {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (q : PairIdx X k)
    (c : ZMod 2) :
    pairPushLin X Y f k (Finsupp.single q c) = Finsupp.single (pairIdxPush f k q) c := by
  unfold pairPushLin
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem swapEnd_pairPushLin {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (z : PairIdx X k →₀ ZMod 2) :
    pairPushLin X Y f k (swapEnd X k z) = swapEnd Y k (pairPushLin X Y f k z) := by
  unfold pairPushLin swapEnd
  rw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
    Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

/-! ## 2. Commuting with the swap is `Λ`-linearity -/

/-- **The criterion.**  An `F₂`-linear map between two target modules that
commutes with their swaps is linear over the whole group ring.  Only two of the
three cases of the induction carry content, and the scalar case is trivial
because `ZMod 2` has two elements, so no scalar-tower instance is needed. -/
theorem smul_of_swap {X Y : TopCat.{0}} {j k : ℕ}
    (F : (PairIdx X j →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx Y k →₀ ZMod 2))
    (hF : ∀ z, F (swapEnd X j z) = swapEnd Y k (F z)) (c : GroupRingZ2)
    (z : PairIdx X j →₀ ZMod 2) : F (c • z) = c • F z := by
  refine MonoidAlgebra.induction_on
    (p := fun c : GroupRingZ2 => F (c • z) = c • F z) c ?_ ?_ ?_
  · intro m
    rcases zmod2_eq_zero_or_one (Multiplicative.toAdd m) with hm | hm
    · have hm1 : m = 1 := by
        show Multiplicative.ofAdd (Multiplicative.toAdd m) = Multiplicative.ofAdd (0 : ZMod 2)
        rw [hm]
      have hone : (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) m : GroupRingZ2) = 1 := by
        rw [hm1, map_one]
      rw [hone, one_smul, one_smul]
    · have hm1 : m = Multiplicative.ofAdd (1 : ZMod 2) := by
        show Multiplicative.ofAdd (Multiplicative.toAdd m) = Multiplicative.ofAdd (1 : ZMod 2)
        rw [hm]
      have hgen : (MonoidAlgebra.of (ZMod 2) (Multiplicative (ZMod 2)) m : GroupRingZ2)
          = groupRingGen := by
        rw [hm1]
        rfl
      rw [hgen, groupRingGen_smul, groupRingGen_smul]
      exact hF z
  · intro c₁ c₂ h₁ h₂
    rw [add_smul, map_add, h₁, h₂, add_smul]
  · intro r c hc
    rcases zmod2_eq_zero_or_one r with hr | hr
    · rw [hr, zero_smul]
      simp
    · rw [hr, one_smul]
      exact hc

theorem pairPushLin_smul {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (c : GroupRingZ2)
    (z : PairIdx X k →₀ ZMod 2) :
    pairPushLin X Y f k (c • z) = c • pairPushLin X Y f k z :=
  smul_of_swap (pairPushLin X Y f k) (swapEnd_pairPushLin f k) c z

/-- The pushforward as a map of `Λ`-modules. -/
def pairPushGRLin (X Y : TopCat.{0}) (f : X ⟶ Y) (k : ℕ) :
    (PairIdx X k →₀ ZMod 2) →ₗ[GroupRingZ2] (PairIdx Y k →₀ ZMod 2) where
  toFun := pairPushLin X Y f k
  map_add' u v := map_add (pairPushLin X Y f k) u v
  map_smul' c z := pairPushLin_smul f k c z

/-- The pushforward along the identity is the identity. -/
theorem pairIdxPush_id (X : TopCat.{0}) (k : ℕ) (q : PairIdx X k) :
    pairIdxPush (𝟙 X) k q = q := by
  obtain ⟨p, ρ, τ⟩ := q
  show (⟨p, (pushSimplex (𝟙 X) p.val.1 ρ, pushSimplex (𝟙 X) p.val.2 τ)⟩ : PairIdx X k)
      = ⟨p, (ρ, τ)⟩
  unfold pushSimplex
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- The pushforward respects composition. -/
theorem pairIdxPush_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ)
    (q : PairIdx X k) :
    pairIdxPush g k (pairIdxPush f k q) = pairIdxPush (f ≫ g) k q := by
  obtain ⟨p, ρ, τ⟩ := q
  show (⟨p, (pushSimplex g p.val.1 (pushSimplex f p.val.1 ρ),
      pushSimplex g p.val.2 (pushSimplex f p.val.2 τ))⟩ : PairIdx Z k)
    = ⟨p, (pushSimplex (f ≫ g) p.val.1 ρ, pushSimplex (f ≫ g) p.val.2 τ)⟩
  unfold pushSimplex
  rw [CategoryTheory.Functor.map_comp]
  rfl

/-! ## 3. The target differential is natural -/

theorem pushSimplex_faceSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (j : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    pushSimplex f n (faceSimplex X n j σ) = faceSimplex Y n j (pushSimplex f (n + 1) σ) := by
  rw [faceSimplex_eq_restrictSimplex, faceSimplex_eq_restrictSimplex]
  exact restrictSimplex_naturality f (SimplexCategory.δ j) σ

theorem pairPushLin_dLeft {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ) (h : a + b = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    pairPushLin X Y f k (dLeft X (ZMod 2) k a b h σ τ)
      = dLeft Y (ZMod 2) k a b h (pushSimplex f a σ) (pushSimplex f b τ) := by
  cases a with
  | zero =>
      rw [dLeft_zero, dLeft_zero]
      exact map_zero (pairPushLin X Y f k)
  | succ a' =>
      rw [dLeft_succ, dLeft_succ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pairPushLin_single]
      exact congrArg
        (fun ρ => Finsupp.single
          (⟨⟨(a', b), by omega⟩, (ρ, pushSimplex f b τ)⟩ : PairIdx Y k) (1 : ZMod 2))
        (pushSimplex_faceSimplex f a' j σ)

theorem pairPushLin_dRight {X Y : TopCat.{0}} (f : X ⟶ Y) (k a b : ℕ) (h : a + b = k + 1)
    (σ : singularSimplices X a) (τ : singularSimplices X b) :
    pairPushLin X Y f k (dRight X (ZMod 2) k a b h σ τ)
      = dRight Y (ZMod 2) k a b h (pushSimplex f a σ) (pushSimplex f b τ) := by
  cases b with
  | zero =>
      rw [dRight_zero, dRight_zero]
      exact map_zero (pairPushLin X Y f k)
  | succ b' =>
      rw [dRight_succ, dRight_succ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pairPushLin_single]
      exact congrArg
        (fun ρ => Finsupp.single
          (⟨⟨(a, b'), by omega⟩, (pushSimplex f a σ, ρ)⟩ : PairIdx Y k) (1 : ZMod 2))
        (pushSimplex_faceSimplex f b' j τ)

theorem pairPushLin_dGen {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (q : PairIdx X (k + 1)) :
    pairPushLin X Y f k (dGen X (ZMod 2) k q)
      = dGen Y (ZMod 2) k (pairIdxPush f (k + 1) q) := by
  have hpush : dGen Y (ZMod 2) k (pairIdxPush f (k + 1) q)
      = dLeft Y (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property
            (pushSimplex f q.1.val.1 q.2.1) (pushSimplex f q.1.val.2 q.2.2)
        + dRight Y (ZMod 2) k q.1.val.1 q.1.val.2 q.1.property
            (pushSimplex f q.1.val.1 q.2.1) (pushSimplex f q.1.val.2 q.2.2) := rfl
  rw [dGen_eq, map_add, hpush, pairPushLin_dLeft, pairPushLin_dRight]

/-- **The target differential is natural in the space.** -/
theorem dTgt_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (y : PairIdx X (k + 1) →₀ ZMod 2) :
    pairPushLin X Y f k (dTgt X (ZMod 2) k y)
      = dTgt Y (ZMod 2) k (pairPushLin X Y f (k + 1) y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add, map_add]
  · intro q c
    rw [dTgt_single, map_smul, pairPushLin_single, dTgt_single]
    exact congrArg (fun z => c • z) (pairPushLin_dGen f k q)

/-! ## 4. The diagonal is natural -/

theorem phiPair_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (b : WSIndex X k) :
    Finsupp.mapDomain (pairIdxPush f k) (phiPair X k b) = phiPair Y k (wsPush f k b) := by
  have hfun : (pairIdxPush f k ∘ pairIndexToIdx X k)
      = (pairIndexToIdx Y k ∘ pairPush f k) := rfl
  unfold phiPair
  rw [← Finsupp.mapDomain_comp, hfun, Finsupp.mapDomain_comp,
    phiBasis_naturality f (ZMod 2) b]

theorem wsOfHom_srcMapIdx {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X) :
    wsOfHom Y k (srcMapIdx f k b) = wsPush f k (wsOfHom X k b) := rfl

/-- **Steenrod's diagonal is natural in the space**, against `cc-cartan`'s
pushforward on the source. -/
theorem PhiHom_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (y : WTensorSMod X k) :
    pairPushLin X Y f k (PhiHom X k y)
      = PhiHom Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add]
    exact (map_add (PhiHom Y k) _ _).symm
  · intro b c
    rw [PhiHom_single, pairPushLin_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      PhiHom_single, wsOfHom_srcMapIdx]
    exact congrArg (fun z => c • z) (phiPair_naturality f k (wsOfHom X k b))

end

end Steenrod
end CharClass
end GroupApproximation
