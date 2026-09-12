import GroupApproximation.CharClass.MayerVietorisZeroOf
import GroupApproximation.CharClass.CohomologyProductCover

/-!
# A cover by two disjoint opens splits the cohomology, over a field

The coefficient-generic form of `MayerVietorisDisjoint`: if `U ⊔ V = ⊤` and `U ⊓ V` is empty,
the pair of restrictions `H^n(X; K) → H^n(U; K) ⊕ H^n(V; K)` is a linear isomorphism.
Surjectivity is `mvExactSumOf`, whose matching condition is vacuous because the intersection
has no cohomology, and injectivity is `mvExactXOf` (or `mvExactZeroOf` in degree zero).

## Main results

* `isZero_Hmod_of_isEmptyMV` — `H^k(∅; K) = 0`.
* `mvResPairOf_eq_zero_of_disjoint`, `mvResPairOf_surjective_of_disjoint`.
* `mvPairEquivOf` — the splitting, as a `K`-linear equivalence.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **`H^k(∅; K) = 0` in every degree**, over any coefficient ring. -/
theorem isZero_Hmod_of_isEmptyMV (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y]
    [IsEmpty Y] (k : ℕ) : IsZero (Hmod K (TopCat.of Y) k) := by
  haveI : IsEmpty (TopCat.of Y) := inferInstanceAs (IsEmpty Y)
  haveI := isEmpty_singularSimplices (TopCat.of Y) k
  haveI : Subsingleton (singularCochainGroup K (TopCat.of Y) k) :=
    ⟨fun _ _ => cochain_ext (fun τ => (IsEmpty.false τ).elim)⟩
  rw [ModuleCat.isZero_iff_subsingleton]
  constructor
  intro a b
  obtain ⟨φ, hφ, rfl⟩ := exists_cocycleOf a
  obtain ⟨ψ, hψ, rfl⟩ := exists_cocycleOf b
  exact cocycleClassK_congr K (TopCat.of Y) k (Subsingleton.elim φ ψ) hφ hψ

/-- With an empty intersection, a class restricting to zero on both pieces is zero. -/
theorem mvResPairOf_eq_zero_of_disjoint (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ) {x : Hmod K X n}
    (hU : (mvResUOf K U V hUV n).hom x = 0) (hV : (mvResVOf K U V hUV n).hom x = 0) :
    x = 0 := by
  cases n with
  | zero => exact mvExactZeroOf K U V hUV hU hV
  | succ m =>
    obtain ⟨w, hw⟩ := (mvExactXOf K U V hUV m x).1 ⟨hU, hV⟩
    haveI := ModuleCat.subsingleton_of_isZero
      (isZero_Hmod_of_isEmptyMV K ↥(((U : Set X) ∩ (V : Set X) : Set X)) m)
    rw [← hw, Subsingleton.elim w 0, map_zero]

/-- With an empty intersection, every pair of classes on the two pieces comes from a class on
the whole space. -/
theorem mvResPairOf_surjective_of_disjoint (K : Type) [Field K] (U V : Opens X)
    (hUV : U ⊔ V = ⊤) [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ)
    (a : Hmod K (mvU U) n) (b : Hmod K (mvU V) n) :
    ∃ x, (mvResUOf K U V hUV n).hom x = a ∧ (mvResVOf K U V hUV n).hom x = b := by
  refine (mvExactSumOf K U V hUV n a b).1 ?_
  haveI := ModuleCat.subsingleton_of_isZero
    (isZero_Hmod_of_isEmptyMV K ↥(((U : Set X) ∩ (V : Set X) : Set X)) n)
  exact Subsingleton.elim _ _

/-- **A cover by two disjoint opens splits the cohomology**, over a field. -/
def mvPairEquivOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ) :
    Hmod K X n ≃ₗ[K] (Hmod K (mvU U) n × Hmod K (mvU V) n) :=
  LinearEquiv.ofBijective
    (LinearMap.prod (mvResUOf K U V hUV n).hom (mvResVOf K U V hUV n).hom)
    ⟨by
      intro x y hxy
      have hU : (mvResUOf K U V hUV n).hom (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.fst hxy
      have hV : (mvResVOf K U V hUV n).hom (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.snd hxy
      have := mvResPairOf_eq_zero_of_disjoint K U V hUV n hU hV
      exact sub_eq_zero.1 this,
     by
      rintro ⟨a, b⟩
      obtain ⟨x, hx, hy⟩ := mvResPairOf_surjective_of_disjoint K U V hUV n a b
      exact ⟨x, Prod.ext hx hy⟩⟩

end

end GroupApproximation.CharClass
