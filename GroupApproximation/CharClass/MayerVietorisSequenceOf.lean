import GroupApproximation.CharClass.MayerVietorisElementOf
import GroupApproximation.CharClass.ProjectiveSpaceCohomology

/-!
# Mayer–Vietoris over a field, packaged as `MVSequenceOf K`

The coefficient-generic form of `MayerVietorisSequence`: the structure
`ProjectiveSpaceCohomology.MVSequenceOf K` for a two-element open cover, built from
`MayerVietorisElementOf`.  The four fields are the honest restrictions (`mvResWVOf` carries
the sign that the chain-level map `biprod.lift ι (−ι')` puts on the composite), so
`exact_sum` is the agreement of the two restrictions to the intersection.
-/

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- **The Mayer–Vietoris sequence of a two-element open cover, with coefficients in a
field `K`**, in the form `ProjectiveSpaceCohomology` and the Leray–Hirsch ladder consume. -/
def mvSequenceOf (K : Type) [Field K] (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    MVSequenceOf K X (mvU U) (mvU V) (mvInter U V) where
  resU n := (mvResUOf K U V hUV n).hom
  resV n := (mvResVOf K U V hUV n).hom
  resWU n := (mvResWUOf K U V hUV n).hom
  resWV n := (mvResWVOf K U V hUV n).hom
  δ n := (mvDeltaOf K U V hUV n).hom
  exact_X n x := mvExactXOf K U V hUV n x
  exact_sum n a b := mvExactSumOf K U V hUV n a b
  exact_W n w := mvExactWOf K U V hUV n w

end

end GroupApproximation.CharClass
