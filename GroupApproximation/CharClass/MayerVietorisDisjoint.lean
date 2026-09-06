import GroupApproximation.CharClass.MayerVietorisZero
import GroupApproximation.CharClass.CohomologyProductCover

/-!
# A cover by two disjoint opens splits the cohomology

If `U ⊔ V = ⊤` and `U ⊓ V` is empty, the pair of restrictions

```text
H^n(X) → H^n(U) ⊕ H^n(V)
```

is an isomorphism.  Both halves are pure Mayer–Vietoris: surjectivity is `mvExactSum`,
whose matching condition is vacuous because the intersection has no cohomology at all,
and injectivity is `mvExactX` (or `mvExactZero` in degree zero), whose connecting map
has nothing to come from.

This is the statement that makes the *top-degree* half of the Künneth computation
reachable without the cross-product isomorphism.  The induction computing
`H^{top}(A × S^n)` by Mayer–Vietoris on hemispheres bottoms out at `S⁰`, where the two
pieces are disjoint; that base case is this lemma, not a Künneth theorem.

## Main results

* `mvResPair_eq_zero_of_disjoint`, `mvResPair_surjective_of_disjoint`.
* `mvPairEquiv` — the splitting, as a linear equivalence.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- With an empty intersection, a class restricting to zero on both pieces is zero. -/
theorem mvResPair_eq_zero_of_disjoint (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ) {x : Hmod2 X n}
    (hU : (mvResU U V hUV n).hom x = 0) (hV : (mvResV U V hUV n).hom x = 0) : x = 0 := by
  cases n with
  | zero => exact mvExactZero U V hUV hU hV
  | succ m =>
    obtain ⟨w, hw⟩ := (mvExactX U V hUV m x).1 ⟨hU, hV⟩
    haveI := ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_of_isEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X)) m)
    rw [← hw, Subsingleton.elim w 0, map_zero]

/-- With an empty intersection, every pair of classes on the two pieces comes from a
class on the whole space: the matching condition of `mvExactSum` is vacuous. -/
theorem mvResPair_surjective_of_disjoint (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ)
    (a : Hmod2 (mvU U) n) (b : Hmod2 (mvU V) n) :
    ∃ x, (mvResU U V hUV n).hom x = a ∧ (mvResV U V hUV n).hom x = b := by
  refine (mvExactSum U V hUV n a b).1 ?_
  haveI := ModuleCat.subsingleton_of_isZero
    (isZero_cohomology_of_isEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X)) n)
  exact Subsingleton.elim _ _

/-- **A cover by two disjoint opens splits the cohomology.** -/
def mvPairEquiv (U V : Opens X) (hUV : U ⊔ V = ⊤)
    [IsEmpty ↥(((U : Set X) ∩ (V : Set X) : Set X))] (n : ℕ) :
    Hmod2 X n ≃ₗ[ZMod 2] (Hmod2 (mvU U) n × Hmod2 (mvU V) n) :=
  LinearEquiv.ofBijective
    (LinearMap.prod (mvResU U V hUV n).hom (mvResV U V hUV n).hom)
    ⟨by
      intro x y hxy
      have hU : (mvResU U V hUV n).hom (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.fst hxy
      have hV : (mvResV U V hUV n).hom (x - y) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Prod.snd hxy
      have := mvResPair_eq_zero_of_disjoint U V hUV n hU hV
      exact sub_eq_zero.1 this,
     by
      rintro ⟨a, b⟩
      obtain ⟨x, hx, hy⟩ := mvResPair_surjective_of_disjoint U V hUV n a b
      exact ⟨x, Prod.ext hx hy⟩⟩

end

end GroupApproximation.CharClass
