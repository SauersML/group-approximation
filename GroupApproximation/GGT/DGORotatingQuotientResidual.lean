import GroupApproximation.GGT.DGORotatingQuotientRefutation

/-!
# What is left of DGO's Theorem 5.3 when the bookkeeping is stripped out

`GGT/DGORotatingQuotientRefutation.lean` proves that DGO's Theorem 5.3 as this
repository recorded it -- with the finite-order lifting clause on the quotient
-- is false, that clause being the one `GGT/HullSCDGO.lean`'s provenance audit
had already identified as **not one of Theorem 5.3's two conclusions**.  Issue
#50 moved it to `HullSCFilling.RotatingData.finiteOrder_lift`.

This module measures what the rest of the structure costs, and the answer is
nothing.  Four of the five fields `RotatingQuotient` had are supplied by the
quotient `G ⧸ ⟨⟨Rot⟩⟩` itself:

* `Q` and its group structure -- the quotient group;
* `q` -- the canonical projection;
* `surjective` -- `QuotientGroup.mk'_surjective`;
* `ker_eq` -- `QuotientGroup.ker_mk'`.

So `rotatingQuotient_of_dichotomy` below builds the whole conclusion from the
one clause that has content, and the citation `HullSC.DGOQuotientStatement` now
says exactly this and no more:

> for a separated very rotating family, every nonidentity element of the
> subgroup the rotations generate is conjugate into a rotation subgroup or is
> loxodromic.

That is DGO's Theorem 5.3(b) verbatim.  Whoever discharges it owes the
Greendlinger-type lemma of DGO §5.1.3 and nothing else; and whoever owes the
lifting clause owes it where the stabilisers of the action are known, which is
Hull's cone-off and not DGO's theorem.

`nonempty_rotatingQuotient_dot` is the other half of the audit, and it is what
makes the repair a repair rather than a dodge: the model that refutes the
lifting clause **satisfies** what is left, so the statement the repository now
carries is not refuted by it.
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

/-- **The conclusion of DGO's Theorem 5.3, built from the one clause with
content.**  The quotient group, the projection, its surjectivity and its kernel
are the canonical quotient by the subgroup the rotations generate; nothing in
them refers to the geometry, and after issue #50 nothing else is left. -/
def rotatingQuotient_of_dichotomy {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] {C : Set X} {Rot : X → Subgroup G}
    (hdich : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x) :
    RotatingQuotient C Rot where
  Q := G ⧸ rotationNormalClosure C Rot
  group := inferInstance
  q := QuotientGroup.mk' (rotationNormalClosure C Rot)
  surjective := QuotientGroup.mk'_surjective _
  ker_eq := QuotientGroup.ker_mk' _
  rotation_or_loxodromic := hdich

/-- The same, as the `Nonempty` the statement asks for. -/
theorem nonempty_rotatingQuotient_of_dichotomy {G : Type u} [Group G]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X] {C : Set X}
    {Rot : X → Subgroup G}
    (hdich : ∀ g ∈ rotationNormalClosure C Rot, g ≠ 1 →
      (∃ (a : G) (c : X), c ∈ C ∧ a⁻¹ * g * a ∈ Rot c) ∨
        ∀ x : X, IsLoxodromic g x) :
    Nonempty (RotatingQuotient C Rot) :=
  ⟨rotatingQuotient_of_dichotomy hdich⟩

/-! ## The refuting model satisfies what is left -/

/-- **The one-point model of `GGT/DGORotatingQuotientRefutation.lean` satisfies
the conclusion the repository now records.**

This is the check that issue #50's repair is a repair and not a dodge.  The
model refutes the finite-order clause; it does *not* refute the dichotomy, and
therefore does not refute `HullSC.DGOQuotientStatementGeodesic`.  Every
nonidentity element of the kernel is conjugate into `Rot pt = K` by the
conjugator `a = 1`, there being only one apex and only one rotation subgroup. -/
theorem nonempty_rotatingQuotient_dot {G : Type u} [Group G] {K : Subgroup G}
    (hK : K.Normal) :
    Nonempty (RotatingQuotient (Set.univ : Set Dot) (fun _ => K)) := by
  refine nonempty_rotatingQuotient_of_dichotomy ?_
  intro g hg _
  rw [rotationNormalClosure_dot hK] at hg
  refine Or.inl ⟨1, Dot.pt, Set.mem_univ _, ?_⟩
  rw [inv_one, one_mul, mul_one]
  exact hg

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
