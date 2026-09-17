import GroupApproximation.BooneHigman.Metabelian.ChainCharP
import GroupApproximation.BooneHigman.Metabelian.ChainCharZero
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.GroupTheory.Finiteness
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton, part 4: quasi-linear groups

Research node `quasi-linear-groups-satisfy-permutational-boone-higman`, route
`quasi-linear-pbh-via-coordinate-projections`: a finitely generated group embedding in a finite
product `∏ GL_{d_i}(K_i)` over fields embeds in the product of the images of its coordinate
projections, each a finitely generated linear group over a single field, hence (by the two
characteristic nodes) in a finitely presented self-similar group; and the class is closed under
finite products.

* `IsQuasiLinear G`: `G` embeds in `∏_{i < r} GL_{d_i}(K_i)`.
* `linearHostStatement_of_charP_charZero`: the existing `Products.LinearHostStatement` from the
  characteristic-`p` and characteristic-`0` nodes, by a case split on `ringChar K`.
* `quasiLinearHostStatement_of_linearHost`: the coordinate-projection step.
* `quasiLinearHostStatement_of_chain`: the node from all its leaves.

The research node `boone-higman-type-a-class-closed-under-finite-extensions` concerns the class
`B_A`; with `B_A` replaced by `Products.EmbedsInFPSelfSimilarGroup`, the closure needed here is
the proved `Products.embedsInFPSelfSimilarGroup_pi_fin`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- `G` is *quasi-linear*: it embeds in a finite product of general linear groups over fields. -/
def IsQuasiLinear (G : Type) [Group G] : Prop :=
  ∃ (r : ℕ) (K : Fin r → Type) (_ : ∀ i, Field (K i)) (d : Fin r → ℕ)
    (f : G →* ∀ i, Matrix.GeneralLinearGroup (Fin (d i)) (K i)), Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.IsQuasiLinear

/-- **Research node `quasi-linear-groups-satisfy-permutational-boone-higman`**, with `B_A` replaced
by `Products.EmbedsInFPSelfSimilarGroup`. -/
def QuasiLinearHostStatement : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsQuasiLinear G → Products.EmbedsInFPSelfSimilarGroup G

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.QuasiLinearHostStatement

/-- **Linear groups over an arbitrary field**, from the two characteristic nodes. -/
theorem linearHostStatement_of_charP_charZero (hp : CharPLinearHostStatement)
    (hzero : CharZeroLinearHostStatement) : Products.LinearHostStatement := by
  intro K _ n H hH
  by_cases h0 : ringChar K = 0
  · haveI : CharP K 0 := ringChar.of_eq h0
    haveI : CharZero K := CharP.charP_to_charZero K
    exact hzero K n H hH
  · exact hp K (ringChar K) (Nat.pos_of_ne_zero h0) rfl n H hH

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.linearHostStatement_of_charP_charZero

/-- The `i`-th coordinate projection of a homomorphism into a product of general linear groups. -/
def coordHom {G : Type} [Group G] {r : ℕ} {K : Fin r → Type} [∀ i, Field (K i)]
    {d : Fin r → ℕ} (f : G →* ∀ i, Matrix.GeneralLinearGroup (Fin (d i)) (K i)) (i : Fin r) :
    G →* Matrix.GeneralLinearGroup (Fin (d i)) (K i) :=
  (Pi.evalMonoidHom (fun i => Matrix.GeneralLinearGroup (Fin (d i)) (K i)) i).comp f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.coordHom

/-- **The coordinate-projection step.** -/
theorem quasiLinearHostStatement_of_linearHost (hlin : Products.LinearHostStatement) :
    QuasiLinearHostStatement := by
  intro G _ _ hq
  obtain ⟨r, K, _, d, f, hf⟩ := hq
  have hP : ∀ i, Products.EmbedsInFPSelfSimilarGroup (coordHom f i).range := fun i =>
    hlin (K i) (d i) (coordHom f i).range
      ((Group.fg_iff_subgroup_fg (coordHom f i).range).1 (Group.fg_range (coordHom f i)))
  refine (Products.embedsInFPSelfSimilarGroup_pi_fin r
      (fun i => (coordHom f i).range) hP).of_injective
    (f := MonoidHom.pi fun i => (coordHom f i).rangeRestrict) ?_
  intro x y hxy
  apply hf
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.quasiLinearHostStatement_of_linearHost

/-- **Composition for the quasi-linear node** from all leaves of its subtree. -/
theorem quasiLinearHostStatement_of_chain
    (hcoordP : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habsP : CharPElementaryAbsorptionStatement) (hfpP : CharPElementaryFPStatement)
    (hssP : CharPAffineSelfSimilarStatement)
    (hcoord0 : CharZeroPolynomialCoordinatesStatement)
    (habs0 : CharZeroElementaryAbsorptionStatement) (hfp0 : CharZeroElementaryFPStatement)
    (hss0 : CharZeroAffineSelfSimilarStatement) (haff : AffineExtensionFPStatement) :
    QuasiLinearHostStatement :=
  quasiLinearHostStatement_of_linearHost
    (linearHostStatement_of_charP_charZero
      (charPLinearHostStatement_of_chain hcoordP habsP hfpP haff hssP)
      (charZeroLinearHostStatement_of_chain hcoord0 habs0 hfp0 haff hss0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.quasiLinearHostStatement_of_chain

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
