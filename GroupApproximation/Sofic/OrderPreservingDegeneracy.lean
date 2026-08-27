import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# `OrderPreservingRoutingData` is degenerate

`OrderPreservingRoutingData` reads the manuscript's own description of
Hull's quotient — "obtained by adjoining finitely many relators,
**preserves element orders**, and restricts to a surjection from `S`" —
as a literal interface, and derives from it both the printed
torsion-freeness condition and survival of the protected element.  That
derivation is correct, and it is recorded in `TorsionFreeFullMFRadical`
where it belongs.

This file records what the interface costs.  The phrase "preserves
element orders", read as `∀ x, orderOf (q x) = orderOf x`, is strictly
stronger than the clause Hull actually publishes.  Hull's clause (e) is
order *reflection*: every element of the quotient of order `n` is the
image of an element of order `n` — an existential statement, isolated in
`isPowerTorsionFree_of_orderReflecting`, which yields torsion-freeness of
the quotient and nothing more.  The universally quantified reading is a
different and much heavier statement, and the two theorems below say how
much heavier:

* `quotient_injective` / `quotient_bijective`: order preservation forces
  the routing map to be injective, because an element of the kernel would
  have the order of the identity.  Combined with the surjectivity already
  derived from the fifth printed condition, the routing map is an
  isomorphism.
* `defectNormal_eq_top`: the compression defect of the *source* is
  therefore already everything.

So an inhabitant of `OrderPreservingRoutingData` is not a routing at all:
it is an isomorphism onto a group that was already its own compression
defect.  No small-cancellation quotient is ever of this shape, because
adjoining a nontrivial relator kills something.  This is why the discharge
target of the routing program is the injectivity-based chain
`RoutingLemmaData` → `DefectRoutingData`, whose `protected_injOn` field
asks only for injectivity on the two-element protected set `{1, s}`, and
never `OrderPreservingRoutingData`.

Companion to `FiveConditionInsufficiency`: that file records an interface
that assumes too little, this one records an interface that assumes too
much.  Neither existing declaration is changed by either.
-/

namespace GroupApproximation

universe u

namespace OrderPreservingRoutingData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E}
    (R : OrderPreservingRoutingData.{u} D)

local instance degenerateQuotientGroup : Group R.Quotient :=
  R.groupQuotient

/-- **Order preservation forces injectivity.**  If `q x = 1` then `q x` has
the order of the identity, namely one; order preservation transports that
to `x`, and an element of order one is the identity. -/
theorem quotient_injective : Function.Injective R.quotient := by
  refine (injective_iff_map_eq_one R.quotient).mpr ?_
  intro x hx
  have h1 : orderOf (R.quotient x) = 1 := orderOf_eq_one_iff.mpr hx
  rw [R.orderPreserving x] at h1
  exact orderOf_eq_one_iff.mp h1

/-- **The routing map is an isomorphism.**  Injectivity comes from order
preservation, surjectivity from the fifth printed condition. -/
theorem quotient_bijective : Function.Bijective R.quotient :=
  ⟨R.quotient_injective, R.quotient_surjective⟩

/-- The routing map packaged as an isomorphism, so that the degeneracy is
visible in the statement: the "quotient" is a copy of the source. -/
noncomputable def quotientMulEquiv : E ≃* R.Quotient :=
  MulEquiv.ofBijective R.quotient R.quotient_bijective

include R in
/-- **The source is already its own compression defect.**  The fifth
printed condition says the defect maps onto the quotient; the routing map
is injective, so the defect was everything to begin with.

This is the sharp form of the degeneracy: `OrderPreservingRoutingData` can
only be inhabited over a source `E` with `N_comp = E`, which is precisely
the situation in which there is nothing left for a routing construction to
do. -/
theorem defectNormal_eq_top : D.core.defectNormal = ⊤ := by
  apply top_unique
  intro x _
  have hx : R.quotient x ∈ D.core.defectNormal.map R.quotient := by
    rw [R.defect_surjective]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hyx : y = x := R.quotient_injective hxy
  rwa [hyx] at hy

end OrderPreservingRoutingData

end GroupApproximation
