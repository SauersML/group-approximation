import GroupApproximation.CharClass.MayerVietorisElement
import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# Mayer–Vietoris packaged as `cc-projective`'s `MVSequence`

`CharClass/ProjectiveSpaceCohomology.lean` computes `H^*(ℂP^n; F₂)` from a
`structure MVSequence X U V W`: four restrictions and a connecting map, all as additive
maps, with the three exactness statements in element form.  This file builds that
structure for a two-element open cover from `CharClass/MayerVietorisElement.lean`.

Nothing here is new mathematics; it is the packaging that lets the projective-space
induction run.
-/

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **The Mayer–Vietoris sequence of a two-element open cover**, in the form
`ProjectiveSpaceCohomology` consumes. -/
def mvSequence (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVSequence X (mvU U) (mvU V) (mvInter U V) where
  resU n := (mvResU U V hUV n).hom.toAddMonoidHom
  resV n := (mvResV U V hUV n).hom.toAddMonoidHom
  resWU n := (mvResWU U V hUV n).hom.toAddMonoidHom
  resWV n := (mvResWV U V hUV n).hom.toAddMonoidHom
  δ n := (mvDelta U V hUV n).hom.toAddMonoidHom
  exact_X n x := mvExactX U V hUV n x
  exact_sum n a b := mvExactSum U V hUV n a b
  exact_W n w := mvExactW U V hUV n w

end

end GroupApproximation.CharClass
