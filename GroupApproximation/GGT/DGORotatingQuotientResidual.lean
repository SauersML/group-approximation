import GroupApproximation.GGT.DGORotatingQuotientRefutation

/-!
# What is left of DGO's Theorem 5.3 when the bookkeeping is stripped out

`GGT/DGORotatingQuotientRefutation.lean` proves that
`HullSC.DGOQuotientStatement` and its geodesic repair are both false, and that
the clause which fails is `RotatingQuotient.finiteOrder_lift` -- the one that
`GGT/HullSCDGO.lean`'s provenance audit already identified as **not one of
Theorem 5.3's two conclusions**.

This module measures what the rest of the structure costs, and the answer is
nothing.  Four of the five fields of `RotatingQuotient` are supplied by the
quotient `G ⧸ ⟨⟨Rot⟩⟩` itself:

* `Q` and its group structure -- the quotient group;
* `q` -- the canonical projection;
* `surjective` -- `QuotientGroup.mk'_surjective`;
* `ker_eq` -- `QuotientGroup.ker_mk'`.

So `rotatingQuotient_of_dichotomy_of_lift` below builds the whole conclusion
from the two clauses that have content, and the citation
`DGOQuotientStatement` says exactly this and no more:

> for a separated very rotating family, every nonidentity element of the
> subgroup the rotations generate is conjugate into a rotation subgroup or is
> loxodromic (**this is DGO's Theorem 5.3(b)**), and every element of finite
> order of the quotient lifts to an element of the same order (**this is not in
> Theorem 5.3, and the refutation module proves it is not implied by the
> hypotheses either**).

The consequence for the repair is arithmetic.  Deleting `finiteOrder_lift` from
`RotatingQuotient` -- the move already made once in this chain, when the
injectivity radius went to `HullSCFilling.RotatingData.kernel_moves_base` --
leaves a citation with one clause in it, and that clause is verbatim Theorem
5.3(b).  Whoever then discharges it owes the Greendlinger-type lemma of DGO
§5.1.3 and nothing else; and whoever owes the lifting clause owes it where the
stabilisers of the action are known, which is Hull's cone-off and not DGO's
theorem.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry

universe u v

/-- **The subgroup the rotations generate is normal**, being a normal closure.

Registered as an instance because `rotationNormalClosure` is not reducible, so
`Subgroup.normalClosure_normal` is not found through it by synthesis, and
`G ⧸ rotationNormalClosure C Rot` does not elaborate without it. -/
instance rotationNormalClosure_normal {G : Type u} [Group G] {X : Type v}
    (C : Set X) (Rot : X → Subgroup G) :
    (rotationNormalClosure C Rot).Normal := by
  show (Subgroup.normalClosure {g : G | ∃ c ∈ C, g ∈ Rot c}).Normal
  infer_instance

/-- **The conclusion of DGO's Theorem 5.3 as recorded, built from its two
clauses with content.**  The quotient group, the projection, its surjectivity
and its kernel are the canonical quotient by the subgroup the rotations
generate; nothing in them refers to the geometry. -/
def rotatingQuotient_of_dichotomy_of_lift {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {C : Set X} {Rot : X → Subgroup G}
    (hdich : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x)
    (hlift : ∀ y : G ⧸ rotationNormalClosure C Rot, IsOfFinOrder y →
      ∃ g : G, QuotientGroup.mk' (rotationNormalClosure C Rot) g = y ∧
        orderOf g = orderOf y) :
    RotatingQuotient C Rot where
  Q := G ⧸ rotationNormalClosure C Rot
  group := inferInstance
  q := QuotientGroup.mk' (rotationNormalClosure C Rot)
  surjective := QuotientGroup.mk'_surjective _
  ker_eq := QuotientGroup.ker_mk' _
  rotation_or_loxodromic := hdich
  finiteOrder_lift := hlift

/-- The same, as the `Nonempty` the statement asks for. -/
theorem nonempty_rotatingQuotient_of_dichotomy_of_lift {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X] {C : Set X}
    {Rot : X → Subgroup G}
    (hdich : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x)
    (hlift : ∀ y : G ⧸ rotationNormalClosure C Rot, IsOfFinOrder y →
      ∃ g : G, QuotientGroup.mk' (rotationNormalClosure C Rot) g = y ∧
        orderOf g = orderOf y) :
    Nonempty (RotatingQuotient C Rot) :=
  ⟨rotatingQuotient_of_dichotomy_of_lift hdich hlift⟩

/-- **And the dichotomy alone is what a rotating quotient carries back**, so the
reduction above loses nothing: `RotatingQuotient` is the dichotomy together with
the lifting clause, over a quotient that is forced up to isomorphism by
`ker_eq` and `surjective`. -/
theorem rotation_or_loxodromic_of_rotatingQuotient {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X] {C : Set X}
    {Rot : X → Subgroup G} (D : RotatingQuotient C Rot) :
    ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x :=
  D.rotation_or_loxodromic

end HullSC
end GroupApproximation
