import Mathlib.GroupTheory.CoprodI
import GroupApproximation.GGT.DGORotatingQuotientRefutation

/-!
# The free splitting does not repair Theorem 5.3 either

`GGT/DGORotatingQuotientRefutation.lean` refutes DGO's Theorem 5.3 as this
repository recorded it, at the one-point space with `C = univ` and
`Rot = fun _ => K` for a normal `K`.  The clause that fails there is the
finite-order lift, which issue #50 moved to
`HullSCFilling.RotatingData.finiteOrder_lift`.

`GGT/HullSCDGO.lean` proposes a route to that clause: record DGO's Theorem
5.3(a) -- the free splitting `⟨⟨Rot⟩⟩ = ∗_{t ∈ T} t⁻¹ (Rot c_t) t` -- as a
further field, and derive the lift from the Bass-Serre tree of the splitting.
Its own words: *"The order-preserving half of `finiteOrder_lift` is therefore
still owed, and it rests on the splitting."*

**That route is closed**, and this module proves it: the one-point model
satisfies the free splitting too, in exactly the form that note writes down.

    T = PUnit,   apex _ = the point,   conj _ = 1,
    φ = the map ∗_{PUnit} K → G induced by the inclusion of K.

`φ` is injective because a free product over a one-element index set is the
factor itself, its range is `K`, which is what the rotations generate, and the
conjugation clause holds with the trivial conjugator.  So both of Theorem
5.3's printed conclusions -- the splitting and the dichotomy, which
`GGT/DGORotatingQuotientRefutation.lean` also verifies in the model -- hold
where the lifting clause fails, and no combination of them implies it.

The reason is visible once it is stated: the splitting is a statement about the
kernel `K` and its own torsion, and the lifting clause is a statement about
elements of `G` **outside** `K` -- about which the splitting says nothing.  A
finite subgroup of `K` being conjugate into a rotation subgroup does not produce
a preimage of a finite-order element of `G / K`.

So the lifting clause has to be proved where the ambient group and its
stabilisers are in scope, which is Hull's cone-off, not DGO's Theorem 5.3.  That
is where issue #50 put it.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u

/-- **A free product over a one-element index set is the factor itself**, in the
half the splitting needs: every element of `∗_{PUnit} K` is `of a` for an
`a ∈ K`.  Proved by the free product's induction principle -- the identity, a
letter, and a product of two such are all of that form, the index being forced
by `PUnit`. -/
theorem coprodI_of_surjective {G : Type u} [Group G] (K : Subgroup G) :
    Function.Surjective
      (Monoid.CoprodI.of (M := fun _ : PUnit.{u + 1} => ↥K)
        (i := PUnit.unit)) := by
  intro w
  refine Monoid.CoprodI.induction_on w ⟨1, map_one _⟩ ?_ ?_
  · intro i m
    cases i
    exact ⟨m, rfl⟩
  · rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ _ _⟩

/-- **The one-point model satisfies Dahmani-Guirardel-Osin's Theorem 5.3(a).**

The statement is the one written out in `GGT/HullSCDGO.lean` as the field
`freeSplitting`, with `Rot (apex i)` beta-reduced to `K`: an index type, an
apex and a conjugator for each index, and an injective homomorphism from the
free product of the rotation subgroups onto what the rotations generate,
carrying each factor to a conjugate of itself.

Since `GGT/DGORotatingQuotientRefutation.lean` refutes the finite-order lifting
clause in this model, and the dichotomy holds here as well
(`GGT/DGORotatingQuotientResidual.lean` builds the quotient), adding the
splitting to `HullSC.RotatingQuotient` could not have repaired it. -/
theorem exists_freeSplitting_dot {G : Type u} [Group G] {K : Subgroup G}
    (hK : K.Normal) :
    ∃ (T : Type u) (apex : T → Dot) (conj : T → G)
      (φ : Monoid.CoprodI (fun _ : T => ↥K) →* G),
      (∀ i, apex i ∈ (Set.univ : Set Dot)) ∧ Function.Injective φ ∧
        φ.range = rotationNormalClosure (Set.univ : Set Dot) (fun _ => K) ∧
          ∀ (i : T) (x : ↥K),
            φ (Monoid.CoprodI.of (M := fun _ : T => ↥K) (i := i) x)
              = conj i * (x : G) * (conj i)⁻¹ := by
  refine ⟨PUnit.{u + 1}, fun _ => Dot.pt, fun _ => 1,
    Monoid.CoprodI.lift (fun _ => K.subtype), fun _ => Set.mem_univ _, ?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := coprodI_of_surjective K x
    obtain ⟨b, rfl⟩ := coprodI_of_surjective K y
    simp only [Monoid.CoprodI.lift_of] at hxy
    have hab : a = b := Subtype.ext hxy
    rw [hab]
  · rw [rotationNormalClosure_dot hK]
    refine le_antisymm ?_ ?_
    · intro g hg
      obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hg
      refine Monoid.CoprodI.induction_on w ?_ ?_ ?_
      · rw [map_one]
        exact one_mem K
      · intro _ m
        rw [Monoid.CoprodI.lift_of]
        exact m.2
      · intro x y hx hy
        rw [map_mul]
        exact mul_mem hx hy
    · intro g hg
      refine MonoidHom.mem_range.mpr
        ⟨Monoid.CoprodI.of (M := fun _ : PUnit.{u + 1} => ↥K)
          (i := PUnit.unit) ⟨g, hg⟩, ?_⟩
      rw [Monoid.CoprodI.lift_of]
  · intro i x
    show Monoid.CoprodI.lift (fun _ : PUnit.{u + 1} => K.subtype)
        (Monoid.CoprodI.of (M := fun _ : PUnit.{u + 1} => ↥K) (i := i) x)
      = 1 * (x : G) * (1 : G)⁻¹
    rw [Monoid.CoprodI.lift_of, inv_one, one_mul, mul_one]

end HullSC
end GroupApproximation
