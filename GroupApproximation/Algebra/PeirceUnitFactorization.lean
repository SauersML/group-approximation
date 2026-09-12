import GroupApproximation.Algebra.PeirceElementaryUnits
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsReductionProof

/-!
# Two-sided reduction of a unit to supported form

`non_mf_groups_exist.tex`, proof of `thm:mf-quotient-units`, item (a):

> … and every unit `u` of `R` factors as `u = gvh` with `g` and `h` products of
> elementary matrices `e_{ij}(x)` of this matrix ring and
> `v = e_1 + (1-e_1)v(1-e_1)`.

This module proves the reduction behind that clause, for an **arbitrary**
subgroup `N ≤ Rˣ` closed under the two Peirce transvection families of a frame.
`Algebra/PeirceElementaryFactorization.lean` instantiates it at the printed
`N = peirceElementarySubgroup`.

## Relation to the module it is modelled on

`Manuscript/OneSidedMFRadical/MFQuotientUnitsReductionProof.lean` runs the same
three steps — pivot, plant an identity in the second corner, clear its row and
column — and its `unit_reduces_to_supported` is the corresponding statement for
`N = cornerUnitSubgroup R`.  Two things there cannot give the printed clause,
and both are about bookkeeping rather than algebra:

* its conclusion is the one-sided coset relation `Peirce.Congr N u v`, that is
  `u * v⁻¹ ∈ N`, and the printed clause asks for factors on **both** sides;
* transitivity of that relation on the right needs `N` normal, and the
  elementary subgroup is not known to be normal.

So the same three steps are carried out here against `FactorsThrough`, which is
transitive for any subgroup.  The two transvection families enter only through
the hypotheses `hupper` and `hlower`, so no `[Countable R]` and no
`cornerUnitSubgroup` appear.
-/

namespace GroupApproximation
namespace MFQuotientUnits

open Peirce

variable {R : Type} [Ring R]

/-! ### The clearing step -/

/-- **Clearing a corner that is already the identity.**  If the `Q`-corner of a
unit is the identity `Q` of that corner, then one transvection on each side at
`Q` makes it supported off `Q`.

No frame, no decomposition and no pure infiniteness enter: this is the last of
the three reduction steps, and it is the one that is pure idempotent algebra.
Both the frame reduction below and the block reduction of
`Algebra/PeirceBlockFactorization.lean` finish with it. -/
theorem exists_clearing_factorization {N : Subgroup Rˣ} {Q : R} (hQ : Q * Q = Q)
    (hupperQ : ∀ {x : R}, Q * x = x → x * Q = 0 → ∃ w ∈ N, (w : R) = 1 + x)
    (hlowerQ : ∀ {x : R}, Q * x = 0 → x * Q = x → ∃ w ∈ N, (w : R) = 1 + x)
    (v : Rˣ) (hfvf : Q * (v : R) * Q = Q) :
    ∃ v' : Rˣ, FactorsThrough N v v' ∧
      (v' : R) = Q + (1 - Q) * (v' : R) * (1 - Q) := by
  let x := -(Q * (v : R) * (1 - Q))
  have hfx : Q * x = x := by
    calc Q * x = -((Q * Q) * (v : R) * (1 - Q)) := by dsimp [x]; noncomm_ring
      _ = x := by rw [hQ]
  have hxf : x * Q = 0 := by
    calc x * Q = -(Q * (v : R) * (Q - Q * Q)) := by dsimp [x]; noncomm_ring
      _ = 0 := by rw [hQ, sub_self]; simp
  obtain ⟨w, hw, hwval⟩ := hupperQ hfx hxf
  let d := v * w
  have hfd : Q * (d : R) = Q := by
    change Q * ((v * w : Rˣ) : R) = Q
    rw [Units.val_mul, hwval]
    calc Q * ((v : R) * (1 + x))
        = Q * (v : R) - (Q * (v : R) * Q) * (v : R) * (1 - Q) := by
          dsimp [x]; noncomm_ring
      _ = Q * (v : R) - Q * (v : R) * (1 - Q) := by rw [hfvf]
      _ = Q * (v : R) * Q := by noncomm_ring
      _ = Q := hfvf
  let y := -((1 - Q) * (d : R) * Q)
  have hfy : Q * y = 0 := by
    calc Q * y = -((Q - Q * Q) * (d : R) * Q) := by dsimp [y]; noncomm_ring
      _ = 0 := by rw [hQ, sub_self]; simp
  have hyf : y * Q = y := by
    calc y * Q = -((1 - Q) * (d : R) * (Q * Q)) := by dsimp [y]; noncomm_ring
      _ = y := by rw [hQ]
  obtain ⟨z, hz, hzval⟩ := hlowerQ hfy hyf
  let result := z * d
  have hfr : Q * (result : R) = Q := by
    change Q * ((z * d : Rˣ) : R) = Q
    rw [Units.val_mul, hzval, ← mul_assoc, mul_add, mul_one, hfy, add_zero, hfd]
  have hrf : (result : R) * Q = Q := by
    change ((z * d : Rˣ) : R) * Q = Q
    rw [Units.val_mul, hzval]
    calc ((1 + y) * (d : R)) * Q
        = (d : R) * Q - (1 - Q) * (d : R) * (Q * (d : R)) * Q := by
          dsimp [y]; noncomm_ring
      _ = (d : R) * Q - (1 - Q) * (d : R) * Q * Q := by rw [hfd]
      _ = (d : R) * Q - (1 - Q) * (d : R) * Q := by
          rw [mul_assoc ((1 - Q) * (d : R)), hQ]
      _ = Q * (d : R) * Q := by noncomm_ring
      _ = Q := by rw [hfd, hQ]
  refine ⟨result, (FactorsThrough.right N v w hw).trans
    (FactorsThrough.left N d z hz), ?_⟩
  have hfrf : Q * (result : R) * Q = Q := by rw [hfr, hQ]
  noncomm_ring [hfr, hrf, hfrf, hQ]

section Reduction

variable (F : Frame R) {N : Subgroup Rˣ}

/-- The transvection families available to the reduction: `1 + x` is in `N`
whenever `x` sits in the row of a frame idempotent. -/
def UpperFamily (F : Frame R) (N : Subgroup Rˣ) : Prop :=
  ∀ (i : Fin 2) {x : R}, F.e i * x = x → x * F.e i = 0 → ∃ w ∈ N, (w : R) = 1 + x

/-- The transposed family: `1 + x` is in `N` whenever `x` sits in the column of
a frame idempotent. -/
def LowerFamily (F : Frame R) (N : Subgroup Rˣ) : Prop :=
  ∀ (i : Fin 2) {x : R}, F.e i * x = 0 → x * F.e i = x → ∃ w ∈ N, (w : R) = 1 + x

/-- Every frame root is one of the upper transvections, so it lies in `N`. -/
theorem root_mem_of_upperFamily (hupper : UpperFamily F N) (i j : Fin 2)
    (hij : i ≠ j) (c : R) : F.root i j hij c ∈ N := by
  have hl : F.e i * (F.s i * c * F.t j) = F.s i * c * F.t j := by
    show F.s i * F.t i * (F.s i * c * F.t j) = _
    calc F.s i * F.t i * (F.s i * c * F.t j)
        = F.s i * (F.t i * F.s i) * c * F.t j := by noncomm_ring
      _ = F.s i * c * F.t j := by rw [F.ts i]; noncomm_ring
  have hr : (F.s i * c * F.t j) * F.e i = 0 := by
    show F.s i * c * F.t j * (F.s i * F.t i) = 0
    calc F.s i * c * F.t j * (F.s i * F.t i)
        = F.s i * c * (F.t j * F.s i) * F.t i := by noncomm_ring
      _ = 0 := by rw [F.cross j i (Ne.symm hij)]; simp
  obtain ⟨w, hw, hwv⟩ := hupper i hl hr
  have hroot : F.root i j hij c = w := Units.ext (by rw [F.root_val, hwv])
  rw [hroot]
  exact hw

variable (hR : IsPurelyInfiniteSimpleRing R)

include hR

/-- **Pivot.**  One column operation makes the first frame corner nonzero. -/
theorem exists_pivot_factorization (hlower : LowerFamily F N) (u : Rˣ) :
    ∃ v : Rˣ, FactorsThrough N u v ∧ F.coeff v 0 0 ≠ 0 := by
  haveI := hR.isSimpleRing
  have he : F.e 0 * F.e 0 = F.e 0 := F.e_idem 0
  have hene : F.e 0 ≠ 0 := F.e_ne_zero 0
  have huinv : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 :=
    congrArg (Units.val : Rˣ → R) (mul_inv_cancel u)
  have heu : F.e 0 * (u : R) ≠ 0 := by
    intro hz
    apply hene
    calc F.e 0 = (F.e 0 * (u : R)) * ((u⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, huinv, mul_one]
      _ = 0 := by rw [hz, zero_mul]
  have hcorner : ∃ v : Rˣ, FactorsThrough N u v ∧ F.e 0 * (v : R) * F.e 0 ≠ 0 := by
    by_cases hz : F.e 0 * (u : R) * F.e 0 = 0
    · obtain ⟨p, q, hpq⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR heu
      have hl : F.e 0 * ((1 - F.e 0) * q * F.e 0) = 0 := by
        calc F.e 0 * ((1 - F.e 0) * q * F.e 0)
            = (F.e 0 - F.e 0 * F.e 0) * q * F.e 0 := by noncomm_ring
          _ = 0 := by rw [he, sub_self]; simp
      have hr : ((1 - F.e 0) * q * F.e 0) * F.e 0 = (1 - F.e 0) * q * F.e 0 := by
        rw [mul_assoc, he]
      obtain ⟨w, hw, hwval⟩ := hlower 0 hl hr
      refine ⟨u * w, FactorsThrough.right N u w hw, ?_⟩
      have hval : F.e 0 * ((u * w : Rˣ) : R) * F.e 0
          = (F.e 0 * (u : R)) * q * F.e 0 := by
        rw [Units.val_mul, hwval]
        calc F.e 0 * ((u : R) * (1 + (1 - F.e 0) * q * F.e 0)) * F.e 0
            = F.e 0 * (u : R) * F.e 0
              + (F.e 0 * (u : R) - F.e 0 * (u : R) * F.e 0) * q *
                (F.e 0 * F.e 0) := by noncomm_ring
          _ = (F.e 0 * (u : R)) * q * F.e 0 := by
              rw [hz, he, sub_zero, zero_add]
      rw [hval]
      intro hz'
      apply hene
      calc F.e 0 = (p * (F.e 0 * (u : R)) * q) * F.e 0 := by rw [hpq, one_mul]
        _ = p * ((F.e 0 * (u : R)) * q * F.e 0) := by noncomm_ring
        _ = 0 := by rw [hz', mul_zero]
    · exact ⟨u, FactorsThrough.refl _ u, hz⟩
  obtain ⟨v, hv, hne⟩ := hcorner
  refine ⟨v, hv, ?_⟩
  intro hzz
  apply hne
  calc F.e 0 * (v : R) * F.e 0 = F.s 0 * F.coeff v 0 0 * F.t 0 := by
        simp only [Frame.e, Frame.coeff]; noncomm_ring
    _ = 0 := by rw [hzz]; simp

/-- **Planting the identity.**  Two elementary operations make the second frame
corner the identity of that corner. -/
theorem exists_identityCorner_factorization (hupper : UpperFamily F N)
    (hlower : LowerFamily F N) (u : Rˣ) :
    ∃ v : Rˣ, FactorsThrough N u v ∧ F.e 1 * (v : R) * F.e 1 = F.e 1 := by
  obtain ⟨v, huv, hv⟩ := exists_pivot_factorization F hR hlower u
  obtain ⟨p, q, hpq⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR hv
  let rho := q * (1 - p * F.coeff v 0 1)
  let v₁ := v * F.root 0 1 (by decide) rho
  have hfirst : p * F.coeff v₁ 0 1 = 1 := by
    rw [show v₁ = v * F.root 0 1 (by decide) rho from rfl, F.coeff_mul_root,
      if_pos rfl]
    calc p * (F.coeff v 0 1 + F.coeff v 0 0 * rho) =
        p * F.coeff v 0 1 + (p * F.coeff v 0 0 * q) * (1 - p * F.coeff v 0 1) := by
          dsimp [rho]; noncomm_ring
      _ = 1 := by rw [hpq, one_mul]; noncomm_ring
  let c := (1 - F.coeff v₁ 1 1) * p
  let v₂ := F.root 1 0 (by decide) c * v₁
  have hone : F.coeff v₂ 1 1 = 1 := by
    rw [show v₂ = F.root 1 0 (by decide) c * v₁ from rfl, F.coeff_root_mul,
      if_pos rfl]
    dsimp [c]
    rw [mul_assoc, hfirst, mul_one]
    noncomm_ring
  refine ⟨v₂, huv.trans ((FactorsThrough.right N v _
    (root_mem_of_upperFamily F hupper 0 1 (by decide) rho)).trans
      (FactorsThrough.left N v₁ _
        (root_mem_of_upperFamily F hupper 1 0 (by decide) c))), ?_⟩
  calc F.e 1 * (v₂ : R) * F.e 1 = F.s 1 * F.coeff v₂ 1 1 * F.t 1 := by
        simp only [Frame.e, Frame.coeff]; noncomm_ring
    _ = F.e 1 := by rw [hone, mul_one]; rfl

/-- **The printed reduction.**  Every unit factors as `g v h` with `g, h ∈ N`
and `v` supported off the second frame idempotent. -/
theorem exists_supported_factorization (hupper : UpperFamily F N)
    (hlower : LowerFamily F N) (u : Rˣ) :
    ∃ v : Rˣ, FactorsThrough N u v ∧
      (v : R) = F.e 1 + (1 - F.e 1) * (v : R) * (1 - F.e 1) := by
  obtain ⟨v, huv, hfvf⟩ :=
    exists_identityCorner_factorization F hR hupper hlower u
  obtain ⟨v', hvv', hsupp⟩ := exists_clearing_factorization (F.e_idem 1)
    (fun hx hxx => hupper 1 hx hxx) (fun hx hxx => hlower 1 hx hxx) v hfvf
  exact ⟨v', huv.trans hvv', hsupp⟩

end Reduction

end MFQuotientUnits
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnits.exists_clearing_factorization
#audit_axioms GroupApproximation.MFQuotientUnits.root_mem_of_upperFamily
#audit_axioms GroupApproximation.MFQuotientUnits.exists_pivot_factorization
#audit_axioms GroupApproximation.MFQuotientUnits.exists_identityCorner_factorization
#audit_axioms GroupApproximation.MFQuotientUnits.exists_supported_factorization
