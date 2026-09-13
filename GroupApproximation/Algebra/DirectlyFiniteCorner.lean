import Mathlib.Data.Matrix.Basis
import GroupApproximation.Algebra.CornerUnitExtension
import GroupApproximation.Meta.AxiomGuard

/-!
# Corners of a directly finite ring, and matrix units

`non_mf_groups_exist.tex`, the proof of Theorem `thm:core-ring-reflection`
(`\label{thm:core-ring-reflection}`, tex lines 1531–1536):

> For amplification, let $\varphi\colon M_m(R_X)\to A$ be unital with
> $A$ directly finite, and put $e=\varphi(E_{11})$.  The corner $eAe$
> is directly finite: extend a one-sided inverse pair by $1-e$ in $A$.
> Apply the preceding argument to the unital map
> $r\mapsto\varphi(rE_{11})$ into this corner.  Multiplication by the
> other matrix units shows that $\varphi$ kills $M_m(I)$.

Nothing in these sentences uses `R_X`, so this module proves them for an arbitrary
ring `R`, an arbitrary finite index type `n`, and an arbitrary unital ring
homomorphism `φ : Matrix n n R →+* A` into a directly finite ring.

* `isDedekindFiniteMonoid_corner`: the corner `eAe` of a directly finite ring is
  directly finite.  The extension by `1 - e` is `MFQuotientUnits.oneSubAddCornerHom`,
  an injective monoid homomorphism `eAe → A`.
* `matrixUnitCornerHom`: `r ↦ φ (single i i r)`, a unital ring homomorphism into the
  corner at `φ (single i i 1)`.
* `map_eq_zero_of_forall_entry_mem`: if every unital homomorphism from `R` into a
  directly finite ring kills a set `I`, then `φ` kills every matrix with entries in `I`.

"Directly finite" is Mathlib's `IsDedekindFiniteMonoid`.
-/

namespace GroupApproximation

open MFQuotientUnits

universe u

section Corner

variable {A : Type*} [Ring A]

/-- The extension `a ↦ 1 - e + a` of corner elements is injective. -/
theorem oneSubAddCornerHom_injective (e : A) (he : IsIdempotentElem e) :
    Function.Injective (oneSubAddCornerHom e he) := fun a b h =>
  corner_ext (add_left_cancel (show (1 - e) + (a : A) = (1 - e) + (b : A) from h))

/-- **The corner of a directly finite ring is directly finite.**

`non_mf_groups_exist.tex`, proof of `thm:core-ring-reflection` (tex lines 1532–1533):

> The corner $eAe$ is directly finite: extend a one-sided inverse pair by $1-e$ in $A$.

If `a * b = e` in `eAe`, then `(1 - e + a) * (1 - e + b) = 1` in `A`, so
`(1 - e + b) * (1 - e + a) = 1`, that is, `b * a = e`. -/
instance isDedekindFiniteMonoid_corner [IsDedekindFiniteMonoid A] (e : A)
    (he : IsIdempotentElem e) : IsDedekindFiniteMonoid (Corner A e he) :=
  IsDedekindFiniteMonoid.of_injective (oneSubAddCornerHom e he)
    (oneSubAddCornerHom_injective e he)

end Corner

section MatrixUnit

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The image `φ (single i i 1)` of a diagonal matrix unit is idempotent. -/
theorem isIdempotentElem_map_single_one {A : Type*} [Ring A] (φ : Matrix n n R →+* A)
    (i : n) : IsIdempotentElem (φ (Matrix.single i i 1)) := by
  show φ (Matrix.single i i 1) * φ (Matrix.single i i 1) = φ (Matrix.single i i 1)
  rw [← map_mul, Matrix.single_mul_single_same, mul_one]

/-- **The unital map `r ↦ φ(r E_{ii})` into the corner at `φ(E_{ii})`.**

`non_mf_groups_exist.tex`, proof of `thm:core-ring-reflection` (tex lines 1534–1535):

> Apply the preceding argument to the unital map
> $r\mapsto\varphi(rE_{11})$ into this corner.

The printed index `1` is an arbitrary index `i` here. -/
def matrixUnitCornerHom {A : Type*} [Ring A] (φ : Matrix n n R →+* A) (i : n) :
    R →+* Corner A (φ (Matrix.single i i 1)) (isIdempotentElem_map_single_one φ i) where
  toFun r := ⟨φ (Matrix.single i i r), mem_cornerNonUnitalSubring_iff.2
    ⟨by rw [← map_mul, Matrix.single_mul_single_same, one_mul],
     by rw [← map_mul, Matrix.single_mul_single_same, mul_one]⟩⟩
  map_one' := corner_ext rfl
  map_mul' r s := corner_ext (by
    show φ (Matrix.single i i (r * s)) = φ (Matrix.single i i r) * φ (Matrix.single i i s)
    rw [← map_mul, Matrix.single_mul_single_same])
  map_zero' := corner_ext (by
    show φ (Matrix.single i i 0) = 0
    rw [Matrix.single_zero, map_zero])
  map_add' r s := corner_ext (by
    show φ (Matrix.single i i (r + s)) = φ (Matrix.single i i r) + φ (Matrix.single i i s)
    rw [Matrix.single_add, map_add])

@[simp] theorem coe_matrixUnitCornerHom {A : Type*} [Ring A] (φ : Matrix n n R →+* A)
    (i : n) (r : R) :
    ((matrixUnitCornerHom φ i r : Corner A _ _) : A) = φ (Matrix.single i i r) := rfl

/-- **Multiplication by the other matrix units shows that `φ` kills `M_m(I)`.**

`non_mf_groups_exist.tex`, proof of `thm:core-ring-reflection` (tex lines 1535–1536):

> Multiplication by the other matrix units shows that $\varphi$ kills $M_m(I)$.

Hypothesis `hI` is "the preceding argument": every unital homomorphism from `R` into a
directly finite ring (in the universe of `A`) kills `I`.  Applied to the corner map
`matrixUnitCornerHom φ i`, whose target is directly finite by
`isDedekindFiniteMonoid_corner`, it gives `φ (single i i x) = 0` for `x ∈ I`.  Then
`single i j x = single i i x * single i j 1`, and every matrix is the sum of its
entries placed at matrix units. -/
theorem map_eq_zero_of_forall_entry_mem {I : Set R}
    (hI : ∀ (B : Type u) [Ring B] [IsDedekindFiniteMonoid B] (ψ : R →+* B), ∀ x ∈ I, ψ x = 0)
    {A : Type u} [Ring A] [IsDedekindFiniteMonoid A] (φ : Matrix n n R →+* A)
    (M : Matrix n n R) (hM : ∀ i j, M i j ∈ I) : φ M = 0 := by
  rw [Matrix.matrix_eq_sum_single M, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hii : φ (Matrix.single i i (M i j)) = 0 :=
    congrArg Subtype.val (hI _ (matrixUnitCornerHom φ i) (M i j) (hM i j))
  have hsplit :
      Matrix.single i j (M i j) = Matrix.single i i (M i j) * Matrix.single i j 1 := by
    rw [Matrix.single_mul_single_same, mul_one]
  rw [hsplit, map_mul, hii, zero_mul]

end MatrixUnit

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.isDedekindFiniteMonoid_corner
#audit_axioms GroupApproximation.matrixUnitCornerHom
#audit_axioms GroupApproximation.map_eq_zero_of_forall_entry_mem
