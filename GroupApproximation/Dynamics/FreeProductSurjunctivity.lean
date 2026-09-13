import GroupApproximation.Dynamics.DoubleFinitarySite

/-!
# Free products of surjunctive groups

At the trivial subgroup the symmetric double `G *_Γ G` amalgamates nothing, so
it is the free product of its two vertex copies.  The permanence theorem
`isSurjunctive_symmetricDouble` therefore specialises to: the free product of
two copies of a surjunctive group is surjunctive
(`isSurjunctive_coprodI_double`).

The identification `doubleBotEquiv` is what the file supplies.  Mathlib carries
only the one-way comparison `PushoutI.ofCoprodI`; its inverse is built here from
the universal property of the amalgam, since both edge maps out of the trivial
subgroup are trivial and the two coproduct injections therefore cone over them.

The free product here is `Monoid.CoprodI` of the constant `Bool`-indexed family
at `G`, which is the coproduct of the two vertex groups of the double.  It is
not Mathlib's binary `Monoid.Coprod`: that is a separate construction, a
congruence on lists of `M ⊕ N` rather than a transfer of `Monoid.CoprodI`, and
the comparison equivalence between the two forms is not available.
-/

namespace GroupApproximation.Surjunctivity

open Monoid

universe u

variable (G : Type u) [Group G]

/-- Both edge maps out of the trivial subgroup are trivial, so the coproduct
injections cone over them. -/
private theorem coprodOf_comp_doubleMap_bot (b : Bool) :
    (CoprodI.of : DoubleFactor G b →* CoprodI (DoubleFactor G)).comp
        (doubleMap G (⊥ : Subgroup G) b) = 1 := by
  ext x
  have hx : (x : G) = 1 := Subgroup.mem_bot.mp x.2
  simp [doubleMap, hx]

/-- The comparison map from a trivially amalgamated double to the free product,
from the universal property of the amalgam. -/
noncomputable def doubleBotToCoprod :
    SymmetricDouble G (⊥ : Subgroup G) →* CoprodI (DoubleFactor G) :=
  PushoutI.lift (fun b => (CoprodI.of : DoubleFactor G b →* CoprodI (DoubleFactor G))) 1
    (coprodOf_comp_doubleMap_bot G)

private theorem ofCoprodI_comp_doubleBotToCoprod :
    (PushoutI.ofCoprodI : CoprodI (DoubleFactor G) →* SymmetricDouble G (⊥ : Subgroup G)).comp
        (doubleBotToCoprod G) = MonoidHom.id _ :=
  PushoutI.hom_ext_nonempty (by intro b; ext g; simp [doubleBotToCoprod])

private theorem doubleBotToCoprod_comp_ofCoprodI :
    (doubleBotToCoprod G).comp
        (PushoutI.ofCoprodI : CoprodI (DoubleFactor G) →* SymmetricDouble G (⊥ : Subgroup G)) =
      MonoidHom.id _ :=
  CoprodI.ext_hom _ _ (by intro b; ext g; simp [doubleBotToCoprod])

/-- **A trivially amalgamated symmetric double is the free product of its two
vertex copies.** -/
noncomputable def doubleBotEquiv :
    SymmetricDouble G (⊥ : Subgroup G) ≃* CoprodI (DoubleFactor G) where
  toFun := doubleBotToCoprod G
  invFun := PushoutI.ofCoprodI
  left_inv := fun x => DFunLike.congr_fun (ofCoprodI_comp_doubleBotToCoprod G) x
  right_inv := fun x => DFunLike.congr_fun (doubleBotToCoprod_comp_ofCoprodI G) x
  map_mul' := map_mul _

/-- **The free product of two copies of a surjunctive group is surjunctive.** -/
theorem isSurjunctive_coprodI_double (h : IsSurjunctive G) :
    IsSurjunctive (CoprodI (DoubleFactor G)) :=
  (isSurjunctive_symmetricDouble (⊥ : Subgroup G) h).of_mulEquiv (doubleBotEquiv G).symm

end GroupApproximation.Surjunctivity
