import GroupApproximation.CharClass.LIXStepDGenRealTorus
import GroupApproximation.CharClass.CohomologyKunnethTorusOf

/-!
# The fields `circle_two` and `z_inj` on the Künneth model of the mapping torus, over a field

Lane `lix-evenside-n` of the STW Problem LIX strengthening programme
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`, §1.4–1.5).

`lix-coeff`'s `CharClass/CohomologyKunnethTorusOf.lean` models the mapping-torus base as
`KnTwo.torusBaseOf Y n = (Y × S^{2n+1}) × S¹`, with projections `KnTwo.prYOf`, `KnTwo.prS1Of`,
`KnTwo.prSoddOf`, and proves the degreewise Künneth uniqueness for `z = t x` over any field and
any nonzero sphere classes (`KnTwo.tx_inj_degree_of_ne_zeroOf`), in exactly the right-nested,
cast-free shape `Gen.z_inj_of_degreewise` consumes.  This file instantiates the two
bundle-independent Künneth-side fields of `Gen.RealTorusModP` on that model.

## Main results

* `Gen.z_inj_torusOf` — the field `z_inj` on the model, for any nonzero sphere classes.
* `Gen.circle_two_torusOf` — the field `circle_two` on the model.
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace Gen

/-- **The field `z_inj` of `Gen.RealTorusModP` on the Künneth model**, over a field, for any
nonzero classes `σ₁ ∈ H¹(S¹; K)` and `σodd ∈ H^{2n+1}(S^{2n+1}; K)`. -/
theorem z_inj_torusOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (σ₁ : TotalPieceOf K (TopCat.of (Sphere 1)) 1) (hσ₁ : σ₁ ≠ 0)
    (σodd : TotalPieceOf K (TopCat.of (Sphere (2 * n + 1))) (2 * n + 1)) (hσodd : σodd ≠ 0) :
    ∀ u v : TotalHOf K (TopCat.of Y),
      TotalHOf.map K (KnTwo.prYOf Y n) u
          + zClass K (KnTwo.prS1Of Y n) (KnTwo.prSoddOf Y n) σ₁ σodd
            * TotalHOf.map K (KnTwo.prYOf Y n) v = 0 → v = 0 :=
  z_inj_of_degreewise K n (KnTwo.prYOf Y n) (KnTwo.prS1Of Y n) (KnTwo.prSoddOf Y n) σ₁ σodd
    (fun c α β h => KnTwo.tx_inj_degree_of_ne_zeroOf K Y n σ₁ hσ₁ σodd hσodd c α β h)

/-- **The field `circle_two` of `Gen.RealTorusModP` on the Künneth model**: the circle factor
is `Sphere 1`, and `H²(S¹; K) = 0`. -/
theorem circle_two_torusOf (K : Type) [Field K] :
    ∀ a : TotalPieceOf K (TopCat.of (Sphere 1)) (1 + 1), a = 0 :=
  circle_two_sphereOf K

end Gen

#audit_axioms Gen.z_inj_torusOf
#audit_axioms Gen.circle_two_torusOf

end CharClass
end GroupApproximation

end
