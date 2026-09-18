import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreathEmbedConeV
import Mathlib.Data.Finite.Prod
import GroupApproximation.Meta.AxiomGuard

/-!
# The doubled regular action is a commutator

For a commutative group `F`, let `F` act on `F × Bool` by `topPerm f`: left translation by `f`
on the `true` copy and by `f⁻¹` on the `false` copy.  With `halfPerm f` (translation by `f` on
the `true` copy only) and the flip `flipPerm F` of the two copies,

* `commutator_halfPerm_flipPerm`: `⁅halfPerm f, flipPerm F⁆ = topPerm f`;
* `topPerm_mul`: `topPerm (f * g) = topPerm f * topPerm g` (this is where `F` is commutative);
* `coneMap_topPerm_mem`: for cones of one length, `coneMap (topPerm f) 1 ∈ ⁅V, V⁆` whenever
  `V_X ≤ V`, since both `coneMap (halfPerm f) 1` and `coneMap (flipPerm F) 1` lie in `V_X`.

`gcFun P f` is the coordinate function used by the wreath embedding: `P (f * x)` on `(x, true)`
and `1` on the `false` copy.

Route: the identity `topPerm f * flipPerm F * halfPerm f = halfPerm f * flipPerm F` is checked
pointwise, and `conePermHom` carries the commutator into `⁅V_X, V_X⁆ ≤ ⁅V, V⁆`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open scoped commutatorElement

noncomputable section

variable {F : Type*} [Group F]

/-- `(x, true) ↦ (f x, true)`, `(x, false) ↦ (f⁻¹ x, false)`. -/
def topFun (f : F) (i : F × Bool) : F × Bool := (cond i.2 (f * i.1) (f⁻¹ * i.1), i.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.topFun

/-- `topFun f` as a permutation. -/
def topPerm (f : F) : Equiv.Perm (F × Bool) where
  toFun := topFun f
  invFun := topFun f⁻¹
  left_inv := by
    rintro ⟨x, _ | _⟩
    · show ((f⁻¹)⁻¹ * (f⁻¹ * x), false) = (x, false)
      rw [inv_inv, mul_inv_cancel_left]
    · show (f⁻¹ * (f * x), true) = (x, true)
      rw [inv_mul_cancel_left]
  right_inv := by
    rintro ⟨x, _ | _⟩
    · show (f⁻¹ * ((f⁻¹)⁻¹ * x), false) = (x, false)
      rw [inv_inv, inv_mul_cancel_left]
    · show (f * (f⁻¹ * x), true) = (x, true)
      rw [mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.topPerm

theorem topPerm_mul (hF : ∀ a b : F, a * b = b * a) (f g : F) :
    topPerm (f * g) = topPerm f * topPerm g := by
  refine Equiv.ext ?_
  rintro ⟨x, _ | _⟩
  · show ((f * g)⁻¹ * x, false) = (f⁻¹ * (g⁻¹ * x), false)
    rw [mul_inv_rev, hF g⁻¹ f⁻¹, mul_assoc]
  · show (f * g * x, true) = (f * (g * x), true)
    rw [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.topPerm_mul

/-- `(x, true) ↦ (f x, true)`, the identity on the `false` copy. -/
def halfFun (f : F) (i : F × Bool) : F × Bool := (cond i.2 (f * i.1) i.1, i.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.halfFun

/-- `halfFun f` as a permutation. -/
def halfPerm (f : F) : Equiv.Perm (F × Bool) where
  toFun := halfFun f
  invFun := halfFun f⁻¹
  left_inv := by
    rintro ⟨x, _ | _⟩
    · rfl
    · show (f⁻¹ * (f * x), true) = (x, true)
      rw [inv_mul_cancel_left]
  right_inv := by
    rintro ⟨x, _ | _⟩
    · rfl
    · show (f * (f⁻¹ * x), true) = (x, true)
      rw [mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.halfPerm

variable (F) in
/-- Exchanging the two copies of `F`. -/
def flipPerm : Equiv.Perm (F × Bool) where
  toFun i := (i.1, !i.2)
  invFun i := (i.1, !i.2)
  left_inv := by
    rintro ⟨x, _ | _⟩
    · rfl
    · rfl
  right_inv := by
    rintro ⟨x, _ | _⟩
    · rfl
    · rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.flipPerm

theorem topPerm_mul_flipPerm_mul_halfPerm (f : F) :
    topPerm f * flipPerm F * halfPerm f = halfPerm f * flipPerm F := by
  refine Equiv.ext ?_
  rintro ⟨x, _ | _⟩
  · rfl
  · show (f⁻¹ * (f * x), false) = (x, false)
    rw [inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.topPerm_mul_flipPerm_mul_halfPerm

theorem commutator_halfPerm_flipPerm (f : F) : ⁅halfPerm f, flipPerm F⁆ = topPerm f := by
  rw [commutatorElement_def, ← topPerm_mul_flipPerm_mul_halfPerm f, mul_inv_cancel_right,
    mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.commutator_halfPerm_flipPerm

/-- The cone coordinates of a wreath element: `P (f * x)` on `(x, true)`, `1` on `false`. -/
def gcFun {G : Type*} [Group G] (P : F → G) (f : F) (i : F × Bool) : G :=
  cond i.2 (P (f * i.1)) 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.gcFun

variable {X : Type*} {c : F × Bool → List X}

theorem coneMap_topPerm_mem [Finite X] (hsep : ConesSeparated c) {N : ℕ}
    (hlen : ∀ i, (c i).length = N) {V : Subgroup (Equiv.Perm (Cantor X))}
    (hV : higmanThompsonV X ≤ V) (f : F) : coneMap hsep (topPerm f) 1 ∈ ⁅V, V⁆ := by
  have e : conePermHom hsep (topPerm f) =
      ⁅conePermHom hsep (halfPerm f), conePermHom hsep (flipPerm F)⁆ := by
    rw [← commutator_halfPerm_flipPerm f, map_commutatorElement]
  show conePermHom hsep (topPerm f) ∈ ⁅V, V⁆
  rw [e]
  exact Subgroup.commutator_mem_commutator
    (hV (coneMap_mem_higmanThompsonV hsep hlen (halfPerm f)))
    (hV (coneMap_mem_higmanThompsonV hsep hlen (flipPerm F)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.coneMap_topPerm_mem

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
