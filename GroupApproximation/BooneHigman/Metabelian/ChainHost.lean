import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.RingTheory.FiniteType
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton, part 1: the affine elementary host

Research node `char-p-linear-pbh-via-polynomial-self-similar-hosts` (and its characteristic-zero
twin `char-zero-linear-pbh-via-polynomial-self-similar-hosts`) places a finitely generated linear
group inside the *affine elementary group* `R^n ⋊ E_n(R)` over a polynomial ring `R`, which is
finitely presented and acts faithfully and self-similarly on a regular rooted tree.

This module fixes the host shared by both characteristics and by the peer lanes
`bh-met-02`, `bh-met-05` and `bh-met-09`:

* `affineAction n R`: the action of `E_n(R) = elementaryGroup (Fin n) R` on the multiplicative copy
  of `R^n` by matrix-vector multiplication;
* `AffineElementaryGroup n R`: the semidirect product `R^n ⋊ E_n(R)`;
* `AffineExtensionFPStatement`: research node `affine-extension-of-fp-elementary-group-is-fp`
  (lane `bh-met-05`, restated here since no such interface was on disk);
* `embedsInFPSelfSimilarGroup_of_affineHost`: a group embedding in `E_n(R)` embeds in a finitely
  presented self-similar group once the affine host is finitely presented and carries a faithful
  self-similar action;
* `finiteType_int_transfer`, `finiteType_int_of_surjective`: finite generation of a ring as a
  `ℤ`-algebra, independent of the chosen `ℤ`-algebra instance.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The action of the elementary group `E_n(R)` on the multiplicative copy of `R^n`, by
matrix-vector multiplication. -/
def affineAction (n : ℕ) (R : Type) [CommRing R] :
    elementaryGroup (Fin n) R →* MulAut (Multiplicative (Fin n → R)) :=
  (MulAutMultiplicative (Fin n → R)).symm.toMonoidHom.comp
    ((DistribMulAction.toAddAut (Matrix (Fin n) (Fin n) R)ˣ (Fin n → R)).comp
      (elementaryGroup (Fin n) R).subtype)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.affineAction

/-- The affine elementary group `R^n ⋊ E_n(R)`. -/
abbrev AffineElementaryGroup (n : ℕ) (R : Type) [CommRing R] : Type :=
  SemidirectProduct (Multiplicative (Fin n → R)) (elementaryGroup (Fin n) R) (affineAction n R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.AffineElementaryGroup

/-- **Research node `affine-extension-of-fp-elementary-group-is-fp`**: for a finitely generated
commutative ring `R` and `n ≥ 4`, if `E_n(R)` is finitely presented then so is `R^n ⋊ E_n(R)`.
Owned by lane `bh-met-05`; restated here because no such interface was on disk. -/
def AffineExtensionFPStatement : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (n : ℕ), 4 ≤ n →
    Group.IsFinitelyPresented (elementaryGroup (Fin n) R) →
      Group.IsFinitelyPresented (AffineElementaryGroup n R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.AffineExtensionFPStatement

/-- **The host step.**  If the affine host `R^n ⋊ E_n(R)` is finitely presented and acts faithfully
and self-similarly on a tree, then every group embedding in `E_n(R)` embeds in a finitely presented
self-similar group (through `E_n(R) ↪ R^n ⋊ E_n(R)`). -/
theorem embedsInFPSelfSimilarGroup_of_affineHost {R : Type} [CommRing R] {n : ℕ}
    [Group.IsFinitelyPresented (AffineElementaryGroup n R)] {X : Type} [Finite X] [Nontrivial X]
    (ρ : AffineElementaryGroup n R →* Trees.TreeAut X) (hρ : Trees.IsSelfSimilarRep ρ)
    {H : Type*} [Group H] {f : H →* elementaryGroup (Fin n) R} (hf : Function.Injective f) :
    Products.EmbedsInFPSelfSimilarGroup H := by
  have hι : Function.Injective
      ((SemidirectProduct.inr : elementaryGroup (Fin n) R →* AffineElementaryGroup n R).comp f) :=
    (SemidirectProduct.inr_injective (φ := affineAction n R)).comp hf
  exact (Products.embedsInFPSelfSimilarGroup_of_rep ρ hρ).of_injective hι

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.embedsInFPSelfSimilarGroup_of_affineHost

/-- Finite generation as a `ℤ`-algebra does not depend on the `ℤ`-algebra instance: all of them
coincide. -/
theorem finiteType_int_transfer {R : Type} [CommRing R] (inst : Algebra ℤ R)
    (h : @Algebra.FiniteType ℤ R _ _ inst) (inst' : Algebra ℤ R) :
    @Algebra.FiniteType ℤ R _ _ inst' := by
  rwa [Subsingleton.elim inst' inst]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.finiteType_int_transfer

/-- A ring that is a quotient of a polynomial ring over `ℤ` in finitely many variables is a
finitely generated `ℤ`-algebra. -/
theorem finiteType_int_of_surjective {R : Type} [CommRing R] {d : ℕ}
    (f : MvPolynomial (Fin d) ℤ →+* R) (hf : Function.Surjective f) : Algebra.FiniteType ℤ R :=
  Algebra.FiniteType.iff_quotient_mvPolynomial''.mpr ⟨d, f.toIntAlgHom, hf⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.finiteType_int_of_surjective

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
