import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Module.RingHom
import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Group.TypeTags.Hom
import GroupApproximation.Meta.AxiomGuard

/-!
# The derived module of a group (lane bh-met-04)

Research node `fg-metabelian-coprimary-quotients-proof`, step (a)1.  For a group `G` with derived
subgroup `A = [G, G]`, the abelian group `A / [A, A]`, written additively, is a module over
`ℤ[Gᵃᵇ]`: `g` acts by conjugation, and elements of `A` act trivially because conjugation by
`a ∈ A` induces the identity on `A / [A, A]`.  When `G` is metabelian, `[A, A] = 1`, so this is
`A` itself (used in `CoprimaryPieces`).

Main declarations:
* `DerivedModule G := Additive (Abelianization (commutator G))`;
* `dcls a`: the class of `a ∈ [G, G]` in the derived module, with `dcls_mul`, `dcls_one`,
  `dcls_inv`, `dcls_pow`;
* `conj G : G →* AddMonoid.End (DerivedModule G)` and its factorization `conjQ G` through `Gᵃᵇ`;
* the instance `Module (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G)`;
* `of_smul_dcls`: `of (of g) • dcls a = dcls (g a g⁻¹)`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

variable (G : Type*) [Group G]

/-- The derived subgroup made abelian and written additively. -/
abbrev DerivedModule : Type _ := Additive (Abelianization (commutator G))

variable {G}

/-- The class of an element of the derived subgroup in the derived module. -/
def dcls (a : commutator G) : DerivedModule G := Additive.ofMul (Abelianization.of a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.dcls

theorem dcls_mul (a b : commutator G) : dcls (a * b) = dcls a + dcls b := by
  rw [dcls, dcls, dcls, map_mul, ofMul_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.dcls_mul

theorem dcls_one : dcls (1 : commutator G) = 0 := by
  rw [dcls, map_one, ofMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.dcls_one

theorem dcls_inv (a : commutator G) : dcls a⁻¹ = -dcls a := by
  rw [dcls, dcls, map_inv, ofMul_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.dcls_inv

theorem dcls_pow (a : commutator G) (n : ℕ) : dcls (a ^ n) = n • dcls a := by
  rw [dcls, dcls, map_pow, ofMul_pow]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.dcls_pow

/-- Additive endomorphisms of the derived module agree when they agree on classes. -/
theorem endHom_ext {φ ψ : AddMonoid.End (DerivedModule G)} (h : ∀ a, φ (dcls a) = ψ (dcls a)) :
    φ = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
  exact QuotientGroup.induction_on y fun a => h a

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.endHom_ext

/-- Conjugation by `g`, on the derived module. -/
def conjEnd (g : G) : AddMonoid.End (DerivedModule G) :=
  MonoidHom.toAdditive (Abelianization.map (MulAut.conjNormal g).toMonoidHom)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conjEnd

theorem conjEnd_dcls (g : G) (a : commutator G) :
    conjEnd g (dcls a) = dcls (MulAut.conjNormal g a) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conjEnd_dcls

variable (G) in
/-- The conjugation action of `G` on its derived module. -/
def conj : G →* AddMonoid.End (DerivedModule G) where
  toFun := conjEnd
  map_one' := endHom_ext fun a => by
    show conjEnd 1 (dcls a) = dcls a
    rw [conjEnd_dcls, map_one, MulAut.one_apply]
  map_mul' g h := endHom_ext fun a => by
    show conjEnd (g * h) (dcls a) = conjEnd g (conjEnd h (dcls a))
    rw [conjEnd_dcls, conjEnd_dcls, conjEnd_dcls, map_mul, MulAut.mul_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conj

theorem conj_dcls (g : G) (a : commutator G) :
    conj G g (dcls a) = dcls (MulAut.conjNormal g a) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conj_dcls

variable (G) in
/-- Elements of the derived subgroup act trivially on the derived module. -/
theorem commutator_le_ker_conj : commutator G ≤ (conj G).ker := by
  intro x hx
  refine MonoidHom.mem_ker.mpr (endHom_ext fun a => ?_)
  show conjEnd x (dcls a) = dcls a
  have he : MulAut.conjNormal x a =
      (⟨x, hx⟩ : commutator G) * a * (⟨x, hx⟩ : commutator G)⁻¹ :=
    Subtype.ext (MulAut.conjNormal_apply x a)
  rw [conjEnd_dcls, he, dcls_mul, dcls_mul, dcls_inv, add_comm, ← add_assoc, neg_add_cancel,
    zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.commutator_le_ker_conj

variable (G) in
/-- The conjugation action factored through the abelianization. -/
def conjQ : Abelianization G →* AddMonoid.End (DerivedModule G) :=
  QuotientGroup.lift (commutator G) (conj G) (commutator_le_ker_conj G)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conjQ

theorem conjQ_of (g : G) : conjQ G (Abelianization.of g) = conj G g :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.conjQ_of

/-- The `ℤ[Gᵃᵇ]`-module structure on the derived module, by conjugation. -/
instance instModuleDerived : Module (MonoidAlgebra ℤ (Abelianization G)) (DerivedModule G) :=
  Module.compHom (DerivedModule G)
    (MonoidAlgebra.lift ℤ (AddMonoid.End (DerivedModule G)) (Abelianization G)
      (conjQ G)).toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.instModuleDerived

/-- A group element acts on the derived module by conjugation. -/
theorem of_smul (g : G) (m : DerivedModule G) :
    MonoidAlgebra.of ℤ (Abelianization G) (Abelianization.of g) • m = conj G g m :=
  DFunLike.congr_fun (MonoidAlgebra.lift_of (conjQ G) (Abelianization.of g)) m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.of_smul

theorem of_smul_dcls (g : G) (a : commutator G) :
    MonoidAlgebra.of ℤ (Abelianization G) (Abelianization.of g) • dcls a =
      dcls (MulAut.conjNormal g a) :=
  (of_smul g (dcls a)).trans (conj_dcls g a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.of_smul_dcls

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
