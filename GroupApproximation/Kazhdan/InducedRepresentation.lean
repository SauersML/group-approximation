import GroupApproximation.Algebra.FiniteIndexTransversal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The representation induced from a finite-index subgroup

Let `Λ ≤ Γ` have finite index and let `π` be an orthogonal representation of `Λ`
on a real Hilbert space `E`.  This module builds `Ind π`, the orthogonal
representation of `Γ` on the finite direct sum `⊕_{c} E` indexed by the chosen
right-coset representatives of `Algebra/FiniteIndexTransversal.lean`, and proves
the two properties the proof of the Bekka--de la Harpe--Valette finite-index
theorem needs:

* `norm_indFun_constVec_sub_sq` --- the *constant* vector built from a unit
  vector `v` of `E` is moved by `Ind π (g)` by exactly the root-mean-square of
  the amounts by which `v` is moved by the finitely many cocycle values
  `c · g · sec(c·g)⁻¹`.  So an almost invariant vector for `π`, tested against
  a finite subset of `Λ`, becomes an almost invariant vector for `Ind π` tested
  against a finite subset of `Γ` --- with **no loss in the tolerance**, because
  the mean of numbers below `ε` is below `ε`.
* `exists_invariant_of_invariant` --- an invariant vector of `Ind π` has a
  nonzero coordinate at the base index `1`, and that coordinate is invariant
  under `π`.  This is where the normalisation `sec 1 = 1` of the transversal is
  used: it makes the base index a fixed point of `Λ`, so the cocycle degenerates
  to the identity on `Λ` and the coordinate equation reads `π(a) w = w`.

## The construction

With `sec` the chosen representative of the right coset `Λγ`, the space is

```
    Ind E = ⊕_{c ∈ reps} E,       (Ind π (g) f) (c) = π (c · g · sec(c·g)⁻¹) (f (sec (c·g)))
```

`act` is the right action `c · g = sec(c·g)` of `Γ` on the representatives and
`cocycle γ g = γ · g · sec(γ·g)⁻¹` is the associated `Λ`-valued cocycle; both,
and their laws `act_act` and `cocycle_mul`, come from
`Algebra/FiniteIndexTransversal.lean`, which is where the finite-index
combinatorics lives.  That the formula is an isometry is `norm_indFun`:
`Ind π (g)` permutes the coordinates along `act` and then applies isometries
coordinatewise.

Nothing here is specific to property `(T)`; the module is the general finite
induction of an orthogonal representation.  `Kazhdan/KazhdanFiniteIndex.lean`
is the consumer.
-/

namespace GroupApproximation
namespace FiniteIndex

open RightTransversal

universe u v

variable {Γ : Type u} [Group Γ] {Λ : Subgroup Γ}

/-! ## The induced representation -/

variable (tr : RightTransversal Γ Λ) (E : Type v)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The space of the induced representation: the `ℓ²` direct sum of one copy of
`E` for each coset representative. -/
abbrev IndSpace : Type (max u v) := PiLp 2 fun _ : Index tr => E

variable (π : Λ →* (E ≃ₗᵢ[ℝ] E))

/-- The induced action of `g` on the direct sum, as a bare function. -/
def indFun (g : Γ) (f : IndSpace tr E) : IndSpace tr E :=
  WithLp.toLp 2 fun c => π (cocycle tr c.1 g) (f (act tr c g))

@[simp] theorem indFun_apply (g : Γ) (f : IndSpace tr E) (c : Index tr) :
    indFun tr E π g f c = π (cocycle tr c.1 g) (f (act tr c g)) := rfl

theorem indFun_add (g : Γ) (f₁ f₂ : IndSpace tr E) :
    indFun tr E π g (f₁ + f₂) = indFun tr E π g f₁ + indFun tr E π g f₂ := by
  refine PiLp.ext fun c => ?_
  simp [PiLp.add_apply]

theorem indFun_smul (g : Γ) (r : ℝ) (f : IndSpace tr E) :
    indFun tr E π g (r • f) = r • indFun tr E π g f := by
  refine PiLp.ext fun c => ?_
  simp [PiLp.smul_apply]

theorem indFun_one (f : IndSpace tr E) : indFun tr E π 1 f = f := by
  refine PiLp.ext fun c => ?_
  simp

theorem indFun_comp (g h : Γ) (f : IndSpace tr E) :
    indFun tr E π g (indFun tr E π h f) = indFun tr E π (g * h) f := by
  refine PiLp.ext fun c => ?_
  simp only [indFun_apply, act_coe, act_act]
  rw [cocycle_mul, map_mul]
  rfl

/-- **The induced action is isometric.**  It permutes the coordinates along
`act` and applies an isometry in each coordinate. -/
theorem norm_indFun (g : Γ) (f : IndSpace tr E) :
    ‖indFun tr E π g f‖ = ‖f‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  refine Fintype.sum_equiv (actEquiv tr g) _ _ fun c => ?_
  simp

/-- The induced action of `g`, as a linear isometric equivalence. -/
def indEquiv (g : Γ) : IndSpace tr E ≃ₗᵢ[ℝ] IndSpace tr E where
  toFun := indFun tr E π g
  map_add' := indFun_add tr E π g
  map_smul' := indFun_smul tr E π g
  invFun := indFun tr E π g⁻¹
  left_inv f := by
    show indFun tr E π g⁻¹ (indFun tr E π g f) = f
    rw [indFun_comp, inv_mul_cancel, indFun_one]
  right_inv f := by
    show indFun tr E π g (indFun tr E π g⁻¹ f) = f
    rw [indFun_comp, mul_inv_cancel, indFun_one]
  norm_map' := norm_indFun tr E π g

@[simp] theorem indEquiv_apply (g : Γ) (f : IndSpace tr E) :
    indEquiv tr E π g f = indFun tr E π g f := rfl

/-- **The induced representation** `Ind π : Γ →* O(⊕_c E)`. -/
def ind : Γ →* (IndSpace tr E ≃ₗᵢ[ℝ] IndSpace tr E) where
  toFun := indEquiv tr E π
  map_one' := by
    refine LinearIsometryEquiv.ext fun f => ?_
    simpa using indFun_one tr E π f
  map_mul' g h := by
    refine LinearIsometryEquiv.ext fun f => ?_
    simpa using (indFun_comp tr E π g h f).symm

@[simp] theorem ind_apply (g : Γ) (f : IndSpace tr E) :
    ind tr E π g f = indFun tr E π g f := rfl

/-! ## The constant vector -/

/-- The vector of the direct sum all of whose coordinates equal `v`. -/
def constVec (v : E) : IndSpace tr E := WithLp.toLp 2 fun _ => v

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] theorem constVec_apply (v : E) (c : Index tr) : constVec tr E v c = v := rfl

omit [InnerProductSpace ℝ E] in
/-- The squared norm of the constant vector is the number of cosets times the
squared norm of the entry. -/
theorem norm_constVec_sq (v : E) :
    ‖constVec tr E v‖ ^ 2 = (tr.reps.card : ℝ) * ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp

/-- **The displacement of the constant vector**, coordinate by coordinate: the
sum of the squared displacements of `v` under the finitely many cocycle values.
This is the identity that makes induction lossless in the tolerance. -/
theorem norm_indFun_constVec_sub_sq (g : Γ) (v : E) :
    ‖indFun tr E π g (constVec tr E v) - constVec tr E v‖ ^ 2
      = ∑ c : Index tr, ‖π (cocycle tr c.1 g) v - v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PiLp.sub_apply]
  simp

/-! ## Invariant vectors descend -/

/-- **An invariant vector of the induced representation gives an invariant
vector of the original one.**  Its coordinate at the base index is nonzero ---
the coordinates all have the same norm, because `Γ` permutes them transitively
--- and is fixed by `π`, because the base index is fixed by `Λ` and the cocycle
there is the identity. -/
theorem exists_invariant_of_invariant (y : IndSpace tr E) (hy : y ≠ 0)
    (hinv : ∀ g : Γ, ind tr E π g y = y) :
    ∃ w : E, w ≠ 0 ∧ ∀ a : Λ, π a w = w := by
  refine ⟨y (baseIndex tr), ?_, ?_⟩
  · -- some coordinate is nonzero, and every coordinate has the norm of the base one
    obtain ⟨c, hc⟩ : ∃ c : Index tr, y c ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy (PiLp.ext fun c => by simpa using hcon c)
    intro hzero
    have h := congrArg (fun z : IndSpace tr E => z (baseIndex tr)) (hinv c.1)
    simp only [ind_apply, indFun_apply, act_baseIndex_self] at h
    have hnorm : ‖y c‖ = ‖y (baseIndex tr)‖ := by
      rw [← h, LinearIsometryEquiv.norm_map]
    rw [hzero, norm_zero] at hnorm
    exact hc (norm_eq_zero.mp hnorm)
  · intro a
    have h := congrArg (fun z : IndSpace tr E => z (baseIndex tr)) (hinv (a : Γ))
    simp only [ind_apply, indFun_apply, act_baseIndex_of_mem tr a.2,
      cocycle_baseIndex_of_mem tr a.2] at h
    simpa using h

end FiniteIndex
end GroupApproximation
