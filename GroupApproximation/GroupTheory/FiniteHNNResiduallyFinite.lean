import GroupApproximation.GroupTheory.FiniteHNNFreeLabelFaithful

/-!
# Finite-base HNN extensions are residually finite

The faithful free-label action descends along every quotient of its free
label group.  A Britton-reduced nontrivial word emits a nontrivial free word;
residual finiteness of free groups chooses a finite quotient retaining it.
The descended action is then a homomorphism to a finite symmetric group that
detects the original HNN element.
-/

namespace GroupApproximation
namespace FiniteHNNFreeLabelAction

noncomputable section

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {A B : Subgroup G} (phi : A ≃* B)
variable {Q : Type v} [Group Q]

open HNNExtension

abbrev QuotientSpace (G : Type u) (Q : Type v) := G × Q

/-- The left regular base action on a descended label space. -/
def quotientBasePerm (g : G) : Equiv.Perm (QuotientSpace G Q) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

omit [Fintype G] [Group Q] in
@[simp] theorem quotientBasePerm_apply (g x : G) (w : Q) :
    quotientBasePerm (Q := Q) g (x, w) = (g * x, w) := rfl

def quotientBasePermHom : G →* Equiv.Perm (QuotientSpace G Q) where
  toFun := quotientBasePerm
  map_one' := by ext x <;> simp [quotientBasePerm]
  map_mul' g h := by ext x <;> simp [quotientBasePerm, mul_assoc]

/-- Stable permutation after mapping all free labels into `Q`. -/
def quotientStablePerm
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) : Equiv.Perm (QuotientSpace G Q) :=
  let V := baseIntertwiner phi d
  let label : G → Q := fun x =>
    q (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2)
  { toFun := fun p => (V p.1, label p.1 * p.2)
    invFun := fun p =>
      let x := V.symm p.1
      (x, (label x)⁻¹ * p.2)
    left_inv := by rintro ⟨x, w⟩; simp [V, label]
    right_inv := by rintro ⟨x, w⟩; simp [V, label] }

@[simp] theorem quotientStablePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (x : G) (w : Q) :
    quotientStablePerm phi d q (x, w) =
      (baseIntertwiner phi d x,
        q (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2) * w) := rfl

theorem quotientStablePerm_covariance
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (a : A) :
    quotientStablePerm phi d q * quotientBasePerm (Q := Q) (a : G) =
      quotientBasePerm (Q := Q) ((phi a : B) : G) *
        quotientStablePerm phi d q := by
  ext p <;> rcases p with ⟨x, w⟩
  · exact baseIntertwiner_mul_left phi d a x
  · simp only [Equiv.Perm.mul_apply, quotientStablePerm_apply,
      quotientBasePerm_apply, source_transversal_mul_left]

/-- The descended HNN action. -/
def quotientAction
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) :
    HNNExtension G A B phi →* Equiv.Perm (QuotientSpace G Q) :=
  HNNExtension.lift (quotientBasePermHom (G := G) (Q := Q))
    (quotientStablePerm phi d q) (quotientStablePerm_covariance phi d q)

@[simp] theorem quotientAction_of
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (g : G) :
    quotientAction phi d q (HNNExtension.of g) = quotientBasePerm (Q := Q) g := by
  change (quotientBasePermHom (G := G) (Q := Q)) g = _
  rfl

@[simp] theorem quotientAction_t
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) :
    quotientAction phi d q (HNNExtension.t : HNNExtension G A B phi) =
      quotientStablePerm phi d q := by
  simp [quotientAction]

end


end FiniteHNNFreeLabelAction
end GroupApproximation
