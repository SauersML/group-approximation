import GroupApproximation.Leavitt.UniversalLeavitt
import GroupApproximation.Meta.AxiomGuard
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# Nonunique module rank for the binary Leavitt algebras

`non_mf_groups_exist.tex` says of `L_K(1,n)`:

> "Leavitt introduced the algebras `L_K(1,n)` as examples of rings with
> **nonunique module rank**."

The attribution is Leavitt's.  The mathematical assertion — that the rank of a
finitely generated free module over such a ring is not well defined — is proved
here from the five defining relations alone, with no hypothesis on the ring
beyond carrying a `LeavittFamily` (`Leavitt.lean`).

## The isomorphism, and which side it lives on

Read `A` as a **left** `A`-module.  Left `A`-linear endomorphisms of `A` are
exactly the *right* multiplications, so the two maps witnessing the rank
collapse are

* `Φ : A → A × A`,  `x ↦ (x s₀, x s₁)`;
* `Ψ : A × A → A`,  `(u, v) ↦ u t₀ + v t₁`.

`Ψ ∘ Φ = id` is `s₀t₀ + s₁t₁ = 1` (`sum_range`, applied on the right of `x`),
and `Φ ∘ Ψ = id` is the four relations `tᵢsⱼ = δᵢⱼ`.  Note the handedness: it is
the `s`'s that build the column map and the `t`'s that build its inverse, the
opposite pairing from the *right*-module maps `x ↦ (t₀x, t₁x)` and
`(u,v) ↦ s₀u + s₁v`.  Both readings are true; this file formalizes the left one,
because `Module A A` is Mathlib's default and `InvariantBasisNumber` is stated
for left modules.

This is a genuinely different statement from `LeavittFamily.moduleEquivProd`
(`FiniteModuleObstruction.lean`), which produces a bare `Equiv M ≃ M × M` for an
arbitrary module `M` via `x ↦ (t₀ • x, t₁ • x)`.  That map is not in general
`A`-linear — `A`-linearity of it would force `t₀` and `t₁` central — and
`moduleEquivProd` is deliberately only an `Equiv`, enough for the counting
argument it feeds.  The equivalence below is linear, which is exactly what a
statement about module rank requires.

## What is proved

* `LeavittFamily.linearEquivSquare : A ≃ₗ[A] A × A`;
* `LeavittFamily.finOneLinearEquivFinTwo : (Fin 1 → A) ≃ₗ[A] (Fin 2 → A)` — free
  modules of rank one and rank two are isomorphic;
* `LeavittFamily.nonempty_linearEquiv_finSucc` — every *positive* free rank is
  already isomorphic to rank one, hence (`nonempty_linearEquiv_finSuccSucc`) all
  positive free ranks are mutually isomorphic;
* `LeavittFamily.not_invariantBasisNumber : ¬ InvariantBasisNumber A`, and the
  two consequences `¬ RankCondition A`, `¬ StrongRankCondition A`.

Mathlib's `InvariantBasisNumber` (`Mathlib/LinearAlgebra/InvariantBasisNumber.lean`)
is declared for an arbitrary `[Semiring R]`, not only commutative rings, so it is
the right notion here and no bespoke replacement is needed.

## Calibration

Every statement below is over an arbitrary ring carrying a `LeavittFamily`, so
each is vacuous unless such a ring exists.  It does: `UniversalLeavitt.family` is
a `LeavittFamily` on `UniversalLeavitt.BinaryLeavittAlgebra = L_{𝔽₂}(1,2)`, which
`UniversalLeavittOver.lean` proves `Nontrivial` via the stream representation.
The advertised endpoint `UniversalLeavitt.NonuniqueModuleRank` is stated at that
object and carries the `Nontrivial` clause inside it, so it cannot be satisfied
by the zero ring — which fails `InvariantBasisNumber` for the trivial reason
that `Fin 0 → 0` and `Fin 1 → 0` are both a point.
-/

namespace GroupApproximation

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-! ### The two column identities -/

/-- `x s₀ t₀ + x s₁ t₁ = x`: `sum_range` read on the right of `x`.  This is
`Ψ ∘ Φ = id`. -/
theorem mul_s_mul_t (x : A) : x * L.s0 * L.t0 + x * L.s1 * L.t1 = x := by
  rw [mul_assoc, mul_assoc, ← mul_add, L.sum_range, mul_one]

/-- `(u t₀ + v t₁) s₀ = u`: the first component of `Φ ∘ Ψ = id`. -/
theorem add_mul_t_mul_s0 (u v : A) : (u * L.t0 + v * L.t1) * L.s0 = u := by
  rw [add_mul, mul_assoc, mul_assoc, L.t0_s0, L.t1_s0, mul_one, mul_zero, add_zero]

/-- `(u t₀ + v t₁) s₁ = v`: the second component of `Φ ∘ Ψ = id`. -/
theorem add_mul_t_mul_s1 (u v : A) : (u * L.t0 + v * L.t1) * L.s1 = v := by
  rw [add_mul, mul_assoc, mul_assoc, L.t0_s1, L.t1_s1, mul_zero, mul_one, zero_add]

/-! ### The rank collapse -/

/-- **The left regular module is isomorphic to its square.**  `x ↦ (x s₀, x s₁)`
is an isomorphism of left `A`-modules with inverse `(u, v) ↦ u t₀ + v t₁`. -/
def linearEquivSquare : A ≃ₗ[A] A × A where
  toFun x := (x * L.s0, x * L.s1)
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · exact add_mul x y L.s0
    · exact add_mul x y L.s1
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · exact mul_assoc c x L.s0
    · exact mul_assoc c x L.s1
  invFun y := y.1 * L.t0 + y.2 * L.t1
  left_inv x := L.mul_s_mul_t x
  right_inv y := by
    refine Prod.ext ?_ ?_
    · exact L.add_mul_t_mul_s0 y.1 y.2
    · exact L.add_mul_t_mul_s1 y.1 y.2

@[simp] theorem linearEquivSquare_apply (x : A) :
    L.linearEquivSquare x = (x * L.s0, x * L.s1) := rfl

@[simp] theorem linearEquivSquare_symm_apply (y : A × A) :
    L.linearEquivSquare.symm y = y.1 * L.t0 + y.2 * L.t1 := rfl

/-- **Rank one and rank two agree.**  The free left `A`-module on one generator
is isomorphic to the free left `A`-module on two generators. -/
def finOneLinearEquivFinTwo : (Fin 1 → A) ≃ₗ[A] (Fin 2 → A) :=
  (LinearEquiv.funUnique (ι := Fin 1) (R := A) (M := A)).trans
    (L.linearEquivSquare.trans (LinearEquiv.finTwoArrow (R := A) (M := A)).symm)

include L in
/-- Every positive free rank collapses onto rank one. -/
theorem nonempty_linearEquiv_finSucc (n : ℕ) :
    Nonempty (A ≃ₗ[A] (Fin (n + 1) → A)) := by
  induction n with
  | zero => exact ⟨(LinearEquiv.funUnique (ι := Fin 1) (R := A) (M := A)).symm⟩
  | succ n ih =>
      obtain ⟨e⟩ := ih
      exact ⟨(L.linearEquivSquare.trans
        (LinearEquiv.prodCongr (LinearEquiv.refl A A) e)).trans
          (Fin.consLinearEquiv A (fun _ : Fin (n + 1 + 1) => A))⟩

include L in
/-- **All positive free ranks are mutually isomorphic.**  There is no
well-defined rank of a finitely generated free module over a ring carrying a
binary Leavitt family. -/
theorem nonempty_linearEquiv_finSuccSucc (n m : ℕ) :
    Nonempty ((Fin (n + 1) → A) ≃ₗ[A] (Fin (m + 1) → A)) := by
  obtain ⟨e⟩ := L.nonempty_linearEquiv_finSucc n
  obtain ⟨f⟩ := L.nonempty_linearEquiv_finSucc m
  exact ⟨e.symm.trans f⟩

/-! ### Failure of the invariant basis number property -/

include L in
/-- **Nonunique module rank.**  A ring carrying a binary Leavitt family does not
satisfy the invariant basis number property. -/
theorem not_invariantBasisNumber : ¬ InvariantBasisNumber A := by
  intro h
  haveI := h
  have h12 : (1 : ℕ) = 2 := eq_of_fin_equiv A L.finOneLinearEquivFinTwo
  exact absurd h12 (by decide)

include L in
/-- The rank condition fails as well: it implies the invariant basis number
property. -/
theorem not_rankCondition : ¬ RankCondition A := by
  intro h
  haveI := h
  exact L.not_invariantBasisNumber inferInstance

include L in
/-- The strong rank condition fails as well. -/
theorem not_strongRankCondition : ¬ StrongRankCondition A := by
  intro h
  haveI := h
  exact L.not_rankCondition inferInstance

end LeavittFamily

/-! ### Calibration: the invariant basis number property is not vacuously false

`not_invariantBasisNumber` says something about the ring only if some ring does
satisfy `InvariantBasisNumber`.  One does. -/

/-- `ℤ` has the invariant basis number property, so failing it is a real
constraint on the ring rather than a defect of Mathlib's definition. -/
theorem invariantBasisNumber_int : InvariantBasisNumber ℤ := inferInstance

/-! ## The printed sentence, at `L_{𝔽₂}(1,2)` -/

namespace UniversalLeavitt

/-- **The manuscript sentence, as a closed proposition.**  The binary Leavitt
algebra `L_{𝔽₂}(1,2)` is a nontrivial ring whose free left modules of rank one
and rank two are isomorphic — indeed all of whose positive free ranks are
mutually isomorphic — and which therefore fails Mathlib's invariant basis number
property.  The `Nontrivial` clause is part of the statement: without it the
failure of `InvariantBasisNumber` would be the vacuous one enjoyed by the zero
ring. -/
def NonuniqueModuleRank : Prop :=
  Nontrivial BinaryLeavittAlgebra ∧
    Nonempty ((Fin 1 → BinaryLeavittAlgebra) ≃ₗ[BinaryLeavittAlgebra]
      (Fin 2 → BinaryLeavittAlgebra)) ∧
    (∀ n m : ℕ, Nonempty ((Fin (n + 1) → BinaryLeavittAlgebra) ≃ₗ[BinaryLeavittAlgebra]
      (Fin (m + 1) → BinaryLeavittAlgebra))) ∧
    ¬ InvariantBasisNumber BinaryLeavittAlgebra

/-- `L_{𝔽₂}(1,2)` has nonunique module rank. -/
theorem nonuniqueModuleRank : NonuniqueModuleRank :=
  ⟨inferInstance,
    ⟨family.finOneLinearEquivFinTwo⟩,
    family.nonempty_linearEquiv_finSuccSucc,
    family.not_invariantBasisNumber⟩

end UniversalLeavitt

end GroupApproximation

/-! ## Audit -/

#audit_closed_axioms GroupApproximation.UniversalLeavitt.nonuniqueModuleRank

