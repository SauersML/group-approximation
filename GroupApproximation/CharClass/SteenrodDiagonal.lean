import GroupApproximation.CharClass.SteenrodCoboundary
import Mathlib.Data.Finsupp.Basic

/-!
# Steenrod's equivariant diagonal `Φ : W ⊗ S(X) → S(X) ⊗ S(X)`

This packages the cut combinatorics as the chain-level map `cc-cartan` consumes,
with `S_*(X) ⊗ S_*(X)` in bidegree `(a,b)` realised concretely as the free
`ZMod 2`-module on pairs of singular simplices rather than through the monoidal
structure on chain complexes.

## What is here

* `facePair a b σ A B` — the basis element of the pair of faces of `σ` spanned by
  the vertex subsets `A` and `B`, and `0` if either has the wrong dimension.  It
  is the `Finsupp`-valued analogue of `faceVal`, and it is total for the same
  reason.
* `steenrodDiag i a b σ = ∑_{S an (i+1)-cut} facePair a b σ (cutU S) (cutV S)` —
  the `(a,b)`-component of `Φ(e_i ⊗ σ)`.
* `steenrodDiag_naturality` — `Φ` commutes with pushing simplices forward along a
  continuous map, i.e. `Φ` is a natural transformation.
* `steenrodDiag_boundary` — the boundary identity
  `∂Φ(e_{i+1} ⊗ σ) = Φ(e_i ⊗ σ) + T Φ(e_i ⊗ σ) + Φ(e_{i+1} ⊗ ∂σ)`, with the two
  `Φ(e_{i+1} ⊗ ∂σ)` terms written out as the face-deletion sums they are.

## Why nothing new is proved here

The identity is `cut_coboundary_master` of `SteenrodCoboundary.lean` instantiated
at `M := (pairs of simplices) →₀ ZMod 2` and `Θ A B := facePair a b σ A B`.  That
master identity carries an arbitrary abelian group of exponent two precisely so
that the cochain formula and this chain-level formula are two readings of one
proof.
The involution `T` is `Finsupp.mapDomain Prod.swap`, and the master's two low
terms are already the two orders of the same cut, which is what `T` exchanges.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass

noncomputable section

/-! ## 1. The bidegree-`(a,b)` part of `S(X) ⊗ S(X)` -/

/-- The free `ZMod 2`-module on pairs of singular simplices of dimensions `a`
and `b`: the bidegree-`(a,b)` part of `S_*(X) ⊗ S_*(X)`. -/
abbrev tensorTwo (X : TopCat.{0}) (a b : ℕ) : Type :=
  (singularSimplices X a × singularSimplices X b) →₀ ZMod 2

/-- The involution `T` exchanging the two tensor factors. -/
def tensorSwap {X : TopCat.{0}} (a b : ℕ) (z : tensorTwo X a b) : tensorTwo X b a :=
  Finsupp.mapDomain Prod.swap z

theorem tensorTwo_add_self {X : TopCat.{0}} {a b : ℕ} (z : tensorTwo X a b) : z + z = 0 := by
  ext w
  have h2 : ∀ y : ZMod 2, y + y = 0 := by decide
  rw [Finsupp.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  exact h2 _

theorem mapDomain_finset_sum {ι α β M : Type*} [AddCommMonoid M] (f : α → β)
    (s : Finset ι) (g : ι → (α →₀ M)) :
    Finsupp.mapDomain f (∑ i ∈ s, g i) = ∑ i ∈ s, Finsupp.mapDomain f (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finsupp.mapDomain_add, ih, Finset.sum_insert ha]

/-! ## 2. The two faces of a cut, as a basis element -/

/-- The basis element of `S_a(X) ⊗ S_b(X)` given by the two faces of `σ` spanned
by `A` and `B`, and `0` if either subset has the wrong size.  This is the
`Finsupp`-valued analogue of `faceVal`. -/
def facePair {X : TopCat.{0}} (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    (A B : Finset (Fin (n + 1))) : tensorTwo X a b :=
  if hA : A.card = a + 1 then
    if hB : B.card = b + 1 then
      Finsupp.single
        (restrictSimplex (faceOfFinset A hA) σ, restrictSimplex (faceOfFinset B hB) σ) 1
    else 0
  else 0

theorem facePair_swap {X : TopCat.{0}} (a b : ℕ) {n : ℕ} (σ : singularSimplices X n)
    (A B : Finset (Fin (n + 1))) :
    tensorSwap a b (facePair a b σ A B) = facePair b a σ B A := by
  unfold tensorSwap facePair
  by_cases hA : A.card = a + 1
  · by_cases hB : B.card = b + 1
    · rw [dif_pos hA, dif_pos hB, dif_pos hB, dif_pos hA, Finsupp.mapDomain_single]
      rfl
    · rw [dif_pos hA, dif_neg hB, dif_neg hB, Finsupp.mapDomain_zero]
  · by_cases hB : B.card = b + 1
    · rw [dif_neg hA, dif_pos hB, dif_neg hA, Finsupp.mapDomain_zero]
    · rw [dif_neg hA, dif_neg hB, Finsupp.mapDomain_zero]

/-- **Deleting a vertex of the ambient simplex**, for `facePair`.  Same statement
and same proof as `faceVal_faceSimplex`. -/
theorem facePair_faceSimplex {X : TopCat.{0}} (a b n : ℕ) (k : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) (A B : Finset (Fin (n + 1))) :
    facePair a b (faceSimplex X n k σ) A B
      = facePair a b σ (A.map (Fin.succAboveOrderEmb k).toEmbedding)
          (B.map (Fin.succAboveOrderEmb k).toEmbedding) := by
  have hA' : (A.map (Fin.succAboveOrderEmb k).toEmbedding).card = A.card := Finset.card_map _
  have hB' : (B.map (Fin.succAboveOrderEmb k).toEmbedding).card = B.card := Finset.card_map _
  unfold facePair
  by_cases hA : A.card = a + 1
  · by_cases hB : B.card = b + 1
    · rw [dif_pos hA, dif_pos hB, dif_pos (hA'.trans hA), dif_pos (hB'.trans hB)]
      congr 2 <;>
        rw [faceSimplex_eq_restrictSimplex, restrictSimplex_comp, faceOfFinset_comp_delta]
    · rw [dif_pos hA, dif_neg hB, dif_pos (hA'.trans hA), dif_neg (fun h => hB (hB' ▸ h))]
  · rw [dif_neg hA, dif_neg (fun h => hA (hA' ▸ h))]

/-! ## 3. The diagonal -/

/-- **Steenrod's diagonal**, `(a,b)`-component of `Φ(e_i ⊗ σ)`: the sum over the
`(i+1)`-element cut sets of the pair of alternating faces they cut out. -/
def steenrodDiag {X : TopCat.{0}} (i a b : ℕ) {n : ℕ} (σ : singularSimplices X n) :
    tensorTwo X a b :=
  ∑ S ∈ cutIndex (i + 1) n, facePair a b σ (cutU S) (cutV S)

/-- The pushforward of a singular simplex along a continuous map. -/
def pushSimplex {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (σ : singularSimplices X n) :
    singularSimplices Y n :=
  (TopCat.toSSet.map f).app (Opposite.op (⦋n⦌ : SimplexCategory)) σ

theorem facePair_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (a b : ℕ) {n : ℕ}
    (σ : singularSimplices X n) (A B : Finset (Fin (n + 1))) :
    Finsupp.mapDomain (Prod.map (pushSimplex f a) (pushSimplex f b)) (facePair a b σ A B)
      = facePair a b (pushSimplex f n σ) A B := by
  unfold facePair
  by_cases hA : A.card = a + 1
  · by_cases hB : B.card = b + 1
    · rw [dif_pos hA, dif_pos hB, dif_pos hA, dif_pos hB, Finsupp.mapDomain_single]
      have h1 : pushSimplex f a (restrictSimplex (faceOfFinset A hA) σ)
          = restrictSimplex (faceOfFinset A hA) (pushSimplex f n σ) :=
        restrictSimplex_naturality f (faceOfFinset A hA) σ
      have h2 : pushSimplex f b (restrictSimplex (faceOfFinset B hB) σ)
          = restrictSimplex (faceOfFinset B hB) (pushSimplex f n σ) :=
        restrictSimplex_naturality f (faceOfFinset B hB) σ
      show Finsupp.single
          (pushSimplex f a (restrictSimplex (faceOfFinset A hA) σ),
            pushSimplex f b (restrictSimplex (faceOfFinset B hB) σ)) 1 = _
      rw [h1, h2]
    · rw [dif_pos hA, dif_neg hB, dif_pos hA, dif_neg hB, Finsupp.mapDomain_zero]
  · rw [dif_neg hA, dif_neg hA, Finsupp.mapDomain_zero]

/-- **`Φ` is natural in the space.**  This is the property `cc-cartan` cannot
recover from the boundary identity alone. -/
theorem steenrodDiag_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (i a b : ℕ) {n : ℕ}
    (σ : singularSimplices X n) :
    Finsupp.mapDomain (Prod.map (pushSimplex f a) (pushSimplex f b)) (steenrodDiag i a b σ)
      = steenrodDiag i a b (pushSimplex f n σ) := by
  unfold steenrodDiag
  rw [mapDomain_finset_sum]
  exact Finset.sum_congr rfl fun S _ => facePair_naturality f a b σ (cutU S) (cutV S)

theorem tensorSwap_steenrodDiag {X : TopCat.{0}} (i a b : ℕ) {n : ℕ}
    (σ : singularSimplices X n) :
    tensorSwap a b (steenrodDiag i a b σ)
      = ∑ S ∈ cutIndex (i + 1) n, facePair b a σ (cutV S) (cutU S) := by
  unfold tensorSwap steenrodDiag
  rw [mapDomain_finset_sum]
  exact Finset.sum_congr rfl fun S _ => facePair_swap a b σ (cutU S) (cutV S)

/-! ## 4. The boundary identity -/

/-- **The equivariant boundary identity for `Φ`.**  The two sums in the middle
are the `(a,b)`-component of `Φ(e_{i+1} ⊗ ∂σ)`, written out as the face-deletion
sums on the left and right tensor factors; the last two terms are
`Φ(e_i ⊗ σ) + T Φ(e_i ⊗ σ)`.

This is `cut_coboundary_master` at `M := tensorTwo X a b`; the whole
mathematical content lives there. -/
theorem steenrodDiag_boundary {X : TopCat.{0}} (i a b n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (∑ k : Fin (n + 2), steenrodDiag (i + 1) a b (faceSimplex X n k σ))
      = (∑ T ∈ cutIndex (i + 1 + 1) (n + 1), ∑ c ∈ cutU T,
            facePair a b σ ((cutU T).erase c) (cutV T))
        + (∑ T ∈ cutIndex (i + 1 + 1) (n + 1), ∑ c ∈ cutV T,
            facePair a b σ (cutU T) ((cutV T).erase c))
        + steenrodDiag i a b σ
        + tensorSwap b a (steenrodDiag i b a σ) := by
  have hlhs : (∑ k : Fin (n + 2), steenrodDiag (i + 1) a b (faceSimplex X n k σ))
      = ∑ k : Fin (n + 2), ∑ S ∈ cutIndex (i + 1 + 1) n,
          facePair a b σ ((cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k)
            ((cutV (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold steenrodDiag
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [facePair_faceSimplex a b n k σ (cutU S) (cutV S), cutU_map_succAbove k S,
      cutV_map_succAbove k S]
  have hswap : tensorSwap b a (steenrodDiag i b a σ)
      = ∑ T ∈ cutIndex (i + 1) (n + 1), facePair a b σ (cutV T) (cutU T) :=
    tensorSwap_steenrodDiag i b a σ
  rw [hlhs, hswap]
  exact cut_coboundary_master tensorTwo_add_self (i + 1) (fun A B => facePair a b σ A B)

end

end CharClass
end GroupApproximation
