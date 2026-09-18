import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.NonUnitalHomotopy
import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The algebraic free product `A * A` as a pre-C⋆-algebra

Cuntz's algebra `qA` (J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1;
Blackadar, *K-Theory for Operator Algebras*, §17.8) is the kernel of the fold map
`A * A → A` on the full unital C⋆-free product of two copies of `A`.  We construct the free
product as a universal C⋆-algebra, keeping it in the universe of `A`:

* `FTerm A`: formal expressions in two copies of `A`, built with `0, 1, +, -, ·, ℂ-scaling, ⋆`;
* `Rep A`: a pair of `⋆`-homomorphisms `φ, ψ : A → D` into a unital C⋆-algebra `D` in the
  universe of `A`;
* `PreFree A`: formal expressions modulo equality of their values under every `Rep A`;
* the norm of `x : PreFree A` is the supremum over all pairs of the norm of the value of `x`,
  realized through the injective map `toLp` into `ℓ^∞` over all pairs.

The completion of `PreFree A` is the full free product (`QalgCompletion`).

Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(Tikuisis--White--Winter), lane TWWKK-Qalg, work order WO-TWWKK-A2.
-/

namespace GroupApproximation.Full.TWWKK

namespace FreeProd

universe u

noncomputable section

/-- Formal expressions in two copies of `A`. -/
inductive FTerm (A : Type u) : Type u
  | gen₁ : A → FTerm A
  | gen₂ : A → FTerm A
  | zero : FTerm A
  | one : FTerm A
  | add : FTerm A → FTerm A → FTerm A
  | neg : FTerm A → FTerm A
  | mul : FTerm A → FTerm A → FTerm A
  | smul : ℂ → FTerm A → FTerm A
  | adj : FTerm A → FTerm A

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- A **representation of the free product**: a pair of `⋆`-homomorphisms from `A` into a unital
C⋆-algebra in the universe of `A`. -/
structure Rep (A : Type u) [NonUnitalCStarAlgebra A] where
  /-- The target algebra. -/
  D : Type u
  /-- The target is a unital C⋆-algebra. -/
  [inst : CStarAlgebra D]
  /-- The first copy. -/
  φ : A →⋆ₙₐ[ℂ] D
  /-- The second copy. -/
  ψ : A →⋆ₙₐ[ℂ] D

attribute [instance] Rep.inst

/-- The value of a formal expression under a representation. -/
def evalTerm (i : Rep A) : FTerm A → i.D
  | .gen₁ a => i.φ a
  | .gen₂ a => i.ψ a
  | .zero => 0
  | .one => 1
  | .add s t => evalTerm i s + evalTerm i t
  | .neg s => -evalTerm i s
  | .mul s t => evalTerm i s * evalTerm i t
  | .smul c s => c • evalTerm i s
  | .adj s => star (evalTerm i s)

/-- A bound for the values of a formal expression, uniform over all representations. -/
def termBound : FTerm A → ℝ
  | .gen₁ a => ‖a‖
  | .gen₂ a => ‖a‖
  | .zero => 0
  | .one => 1
  | .add s t => termBound s + termBound t
  | .neg s => termBound s
  | .mul s t => termBound s * termBound t
  | .smul c s => ‖c‖ * termBound s
  | .adj s => termBound s

/-- In a unital C⋆-algebra, `‖1‖ ≤ 1` (the zero algebra included). -/
theorem norm_one_le_one (D : Type*) [CStarAlgebra D] : ‖(1 : D)‖ ≤ 1 := by
  have h : ‖(1 : D)‖ * ‖(1 : D)‖ = ‖(1 : D)‖ := by
    rw [← CStarRing.norm_star_mul_self, star_one, one_mul]
  have h0 : 0 ≤ ‖(1 : D)‖ := norm_nonneg _
  nlinarith

/-- The values of a formal expression are bounded uniformly over all representations. -/
theorem norm_evalTerm_le (i : Rep A) : ∀ s : FTerm A, ‖evalTerm i s‖ ≤ termBound s
  | .gen₁ a => NonUnitalStarAlgHom.norm_apply_le i.φ a
  | .gen₂ a => NonUnitalStarAlgHom.norm_apply_le i.ψ a
  | .zero => by
    show ‖(0 : i.D)‖ ≤ 0
    rw [norm_zero]
  | .one => norm_one_le_one i.D
  | .add s t => by
    show ‖evalTerm i s + evalTerm i t‖ ≤ termBound s + termBound t
    exact (norm_add_le _ _).trans (add_le_add (norm_evalTerm_le i s) (norm_evalTerm_le i t))
  | .neg s => by
    show ‖-evalTerm i s‖ ≤ termBound s
    rw [norm_neg]
    exact norm_evalTerm_le i s
  | .mul s t => by
    show ‖evalTerm i s * evalTerm i t‖ ≤ termBound s * termBound t
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg (norm_evalTerm_le i s)
      (norm_evalTerm_le i t) (norm_nonneg _) ((norm_nonneg _).trans (norm_evalTerm_le i t)))
  | .smul c s => by
    show ‖c • evalTerm i s‖ ≤ ‖c‖ * termBound s
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_evalTerm_le i s) (norm_nonneg c)
  | .adj s => by
    show ‖star (evalTerm i s)‖ ≤ termBound s
    rw [norm_star]
    exact norm_evalTerm_le i s

/-- Two formal expressions are identified when they agree under every representation. -/
instance termSetoid (A : Type u) [NonUnitalCStarAlgebra A] : Setoid (FTerm A) where
  r s t := ∀ i : Rep A, evalTerm i s = evalTerm i t
  iseqv := ⟨fun _ _ => rfl, fun h i => (h i).symm, fun h h' i => (h i).trans (h' i)⟩

theorem rel_def {s t : FTerm A} : s ≈ t ↔ ∀ i : Rep A, evalTerm i s = evalTerm i t :=
  Iff.rfl

/-- The algebraic free product of two copies of `A` with a unit adjoined, as a quotient of formal
expressions.  It lives in the universe of `A`. -/
def PreFree (A : Type u) [NonUnitalCStarAlgebra A] : Type u :=
  Quotient (termSetoid A)

/-- The class of a formal expression. -/
def mk (s : FTerm A) : PreFree A :=
  Quotient.mk (termSetoid A) s

theorem mk_eq_mk {s t : FTerm A} (h : ∀ i : Rep A, evalTerm i s = evalTerm i t) :
    mk s = mk t :=
  Quotient.sound (rel_def.mpr h)

theorem exists_mk (x : PreFree A) : ∃ s : FTerm A, mk s = x :=
  Quotient.exists_rep x

/-- The value of an element of `PreFree A` under a representation. -/
def evalQ (i : Rep A) : PreFree A → i.D :=
  Quotient.lift (s := termSetoid A) (evalTerm i) (fun _ _ h => rel_def.mp h i)

theorem evalQ_mk (i : Rep A) (s : FTerm A) : evalQ i (mk s) = evalTerm i s :=
  rfl

/-! ## Operations -/

instance : Zero (PreFree A) := ⟨mk .zero⟩

instance : One (PreFree A) := ⟨mk .one⟩

instance : Add (PreFree A) :=
  ⟨Quotient.lift₂ (s₁ := termSetoid A) (s₂ := termSetoid A) (fun s t => mk (.add s t))
    fun _ _ _ _ h₁ h₂ => mk_eq_mk fun i =>
      congrArg₂ (fun a b : i.D => a + b) (rel_def.mp h₁ i) (rel_def.mp h₂ i)⟩

instance : Mul (PreFree A) :=
  ⟨Quotient.lift₂ (s₁ := termSetoid A) (s₂ := termSetoid A) (fun s t => mk (.mul s t))
    fun _ _ _ _ h₁ h₂ => mk_eq_mk fun i =>
      congrArg₂ (fun a b : i.D => a * b) (rel_def.mp h₁ i) (rel_def.mp h₂ i)⟩

instance : Neg (PreFree A) :=
  ⟨Quotient.lift (s := termSetoid A) (fun s => mk (.neg s))
    fun _ _ h => mk_eq_mk fun i => congrArg (fun a : i.D => -a) (rel_def.mp h i)⟩

instance : SMul ℂ (PreFree A) :=
  ⟨fun c => Quotient.lift (s := termSetoid A) (fun s => mk (.smul c s))
    fun _ _ h => mk_eq_mk fun i => congrArg (fun a : i.D => c • a) (rel_def.mp h i)⟩

instance : Star (PreFree A) :=
  ⟨Quotient.lift (s := termSetoid A) (fun s => mk (.adj s))
    fun _ _ h => mk_eq_mk fun i => congrArg (fun a : i.D => star a) (rel_def.mp h i)⟩

instance : Sub (PreFree A) := ⟨fun x y => x + -y⟩

instance : SMul ℕ (PreFree A) := ⟨fun n x => (n : ℂ) • x⟩

instance : SMul ℤ (PreFree A) := ⟨fun n x => (n : ℂ) • x⟩

instance : NatCast (PreFree A) := ⟨fun n => (n : ℂ) • (1 : PreFree A)⟩

instance : IntCast (PreFree A) := ⟨fun n => (n : ℂ) • (1 : PreFree A)⟩

/-- Powers, by recursion. -/
def preNpow : ℕ → PreFree A → PreFree A
  | 0, _ => 1
  | n + 1, x => preNpow n x * x

instance : Pow (PreFree A) ℕ := ⟨fun x n => preNpow n x⟩

/-! ## The embedding into the product over all representations -/

/-- All values of an element, as a point of the product over all representations. -/
def toPi (x : PreFree A) : ∀ i : Rep A, i.D :=
  fun i => evalQ i x

theorem toPi_injective : Function.Injective (toPi (A := A)) := by
  intro x y h
  obtain ⟨s, rfl⟩ := exists_mk x
  obtain ⟨t, rfl⟩ := exists_mk y
  exact mk_eq_mk fun i => congrFun h i

theorem toPi_zero : toPi (0 : PreFree A) = 0 :=
  rfl

theorem toPi_one : toPi (1 : PreFree A) = 1 :=
  rfl

theorem toPi_add (x y : PreFree A) : toPi (x + y) = toPi x + toPi y := by
  obtain ⟨s, rfl⟩ := exists_mk x
  obtain ⟨t, rfl⟩ := exists_mk y
  rfl

theorem toPi_mul (x y : PreFree A) : toPi (x * y) = toPi x * toPi y := by
  obtain ⟨s, rfl⟩ := exists_mk x
  obtain ⟨t, rfl⟩ := exists_mk y
  rfl

theorem toPi_neg (x : PreFree A) : toPi (-x) = -toPi x := by
  obtain ⟨s, rfl⟩ := exists_mk x
  rfl

theorem toPi_smul (c : ℂ) (x : PreFree A) : toPi (c • x) = c • toPi x := by
  obtain ⟨s, rfl⟩ := exists_mk x
  rfl

theorem toPi_star (x : PreFree A) : toPi (star x) = star (toPi x) := by
  obtain ⟨s, rfl⟩ := exists_mk x
  rfl

theorem toPi_sub (x y : PreFree A) : toPi (x - y) = toPi x - toPi y :=
  ((toPi_add x (-y)).trans (congrArg (fun z => toPi x + z) (toPi_neg y))).trans
    (sub_eq_add_neg (toPi x) (toPi y)).symm

theorem toPi_nsmul (n : ℕ) (x : PreFree A) : toPi (n • x) = n • toPi x :=
  (toPi_smul (n : ℂ) x).trans (Nat.cast_smul_eq_nsmul ℂ n (toPi x))

theorem toPi_zsmul (n : ℤ) (x : PreFree A) : toPi (n • x) = n • toPi x :=
  (toPi_smul (n : ℂ) x).trans (Int.cast_smul_eq_zsmul ℂ n (toPi x))

theorem toPi_natCast (n : ℕ) : toPi (n : PreFree A) = n :=
  (toPi_smul (n : ℂ) (1 : PreFree A)).trans
    ((Nat.cast_smul_eq_nsmul ℂ n (1 : ∀ i : Rep A, i.D)).trans (nsmul_one n))

theorem toPi_intCast (n : ℤ) : toPi (n : PreFree A) = n :=
  (toPi_smul (n : ℂ) (1 : PreFree A)).trans
    ((Int.cast_smul_eq_zsmul ℂ n (1 : ∀ i : Rep A, i.D)).trans (zsmul_one n))

theorem toPi_npow (x : PreFree A) : ∀ n : ℕ, toPi (x ^ n) = toPi x ^ n
  | 0 => (pow_zero (toPi x)).symm
  | n + 1 => ((toPi_mul (x ^ n) x).trans
      (congrArg (fun z => z * toPi x) (toPi_npow x n))).trans (pow_succ (toPi x) n).symm

/-! ## Algebraic structure -/

instance instRing : Ring (PreFree A) :=
  Function.Injective.ring toPi toPi_injective toPi_zero toPi_one toPi_add toPi_mul toPi_neg
    toPi_sub toPi_nsmul toPi_zsmul toPi_npow toPi_natCast toPi_intCast

/-- `toPi` as an additive homomorphism. -/
def toPiAdd : PreFree A →+ ∀ i : Rep A, i.D where
  toFun := toPi
  map_zero' := toPi_zero
  map_add' := toPi_add

instance instModule : Module ℂ (PreFree A) :=
  Function.Injective.module ℂ toPiAdd toPi_injective toPi_smul

theorem smul_mul_pre (c : ℂ) (x y : PreFree A) : c • x * y = c • (x * y) :=
  toPi_injective (by rw [toPi_mul, toPi_smul, toPi_smul, toPi_mul, smul_mul_assoc])

theorem mul_smul_pre (c : ℂ) (x y : PreFree A) : x * c • y = c • (x * y) :=
  toPi_injective (by rw [toPi_mul, toPi_smul, toPi_smul, toPi_mul, mul_smul_comm])

instance instAlgebra : Algebra ℂ (PreFree A) :=
  Algebra.ofModule smul_mul_pre mul_smul_pre

instance instStarRing : StarRing (PreFree A) where
  star_involutive x := toPi_injective (by rw [toPi_star, toPi_star, star_star])
  star_mul x y := toPi_injective (by
    rw [toPi_star, toPi_mul, toPi_mul, toPi_star, toPi_star, star_mul])
  star_add x y := toPi_injective (by
    rw [toPi_star, toPi_add, toPi_add, toPi_star, toPi_star, star_add])

instance instStarModule : StarModule ℂ (PreFree A) where
  star_smul c x := toPi_injective (by
    rw [toPi_star, toPi_smul, toPi_smul, toPi_star, star_smul])

end

end FreeProd

end GroupApproximation.Full.TWWKK
