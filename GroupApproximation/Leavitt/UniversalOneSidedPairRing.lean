import GroupApproximation.Leavitt.ProperlyInfiniteUnit
import GroupApproximation.Leavitt.UniversalLeavittOver
import GroupApproximation.PropertyT.FinitelyGeneratedRing
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot

/-!
# The universal one-sided pair ring `𝒞`

`non_mf_groups_exist.tex`, introduction and `thm:full-defect-ring`:

> This happens once, in the ring `𝒞` with generators `s₀,s₁,t₀,t₁` and
> relations `tᵢsⱼ = δᵢⱼ`, and the group `B = EL₄(𝒞)` then maps to every
> `EL_n(R)` below with normally generating image.

`𝒞` is the quotient of the free ring on four generators by the four relations
`tᵢsⱼ = δᵢⱼ` — and by **nothing else**: there is no sum relation
`s₀t₀ + s₁t₁ = 1`, and the base ring is `ℤ`, not a field.  So `𝒞` is exactly
the universal ring carrying a properly infinite unit in the sense of
`RankDescent.ProperlyInfiniteUnit`, and the printed Lemma [two copies] says
that the hypothesis of `thm:full-defect-ring` is precisely a ring map out of
`𝒞` whose image contains the four elements.

## What is proved here

* `unit`, the tautological properly infinite unit of `𝒞`;
* `lift`, the universal property: every properly infinite unit in a ring `A`
  is the image of `unit` under a unique-up-to-generators ring map `𝒞 → A`;
* `Nontrivial 𝒞`, by mapping to the binary Leavitt algebra over `𝔽₂` — a
  Leavitt family is in particular a properly infinite unit, which is the only
  place the extra Leavitt relation is used, and it is used only in the target;
* `Countable 𝒞` and `isFinitelyGeneratedRing`, the two hypotheses the printed
  proof needs of `𝒞`: countability for `thm:compression-criterion` and finite
  generation for the Ershov--Jaikin-Zapirain theorem.

`𝒞` is *not* claimed to be nonzero for any deeper reason than the existence of
one properly infinite unit somewhere; no faithfulness of any representation is
asserted.
-/

namespace GroupApproximation
namespace UniversalPair

open RankDescent

/-! ## A properly infinite unit out of a Leavitt family -/

/-- A binary Leavitt family is in particular a properly infinite unit: the four
relations `tᵢsⱼ = δᵢⱼ` are among its axioms, and the sum relation is not
used. -/
def ofLeavittFamily {A : Type*} [Ring A] (L : LeavittFamily A) :
    ProperlyInfiniteUnit A where
  v := ![L.s0, L.s1]
  w := ![L.t0, L.t1]
  w_mul_v := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]

/-! ## The presentation -/

/-- Names of the four generators `s₀, s₁, t₀, t₁`. -/
abbrev Generator := Fin 4

/-- The two section generators. -/
def sIdx : Fin 2 → Generator := ![0, 1]

/-- The two retraction generators. -/
def tIdx : Fin 2 → Generator := ![2, 3]

/-- Noncommutative polynomials over `ℤ` in the four generators. -/
abbrev Free := FreeAlgebra ℤ Generator

/-- The four relations `tᵢsⱼ = δᵢⱼ`, and no others. -/
inductive Relation : Free → Free → Prop
  | delta (i j : Fin 2) :
      Relation (FreeAlgebra.ι ℤ (tIdx i) * FreeAlgebra.ι ℤ (sIdx j))
        (if i = j then 1 else 0)

/-- **The universal one-sided pair ring `𝒞`.** -/
abbrev UniversalPairRing := RingQuot Relation

/-- The quotient map from noncommutative polynomials. -/
def quotientMap : Free →ₐ[ℤ] UniversalPairRing := RingQuot.mkAlgHom ℤ Relation

/-- A named generator in the quotient. -/
def gen (g : Generator) : UniversalPairRing := quotientMap (FreeAlgebra.ι ℤ g)

/-- **The tautological properly infinite unit of `𝒞`.** -/
def unit : ProperlyInfiniteUnit UniversalPairRing where
  v i := gen (sIdx i)
  w i := gen (tIdx i)
  w_mul_v := by
    intro i j
    have h := RingQuot.mkAlgHom_rel ℤ (Relation.delta i j)
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rw [if_pos rfl] at h
      simpa [gen, quotientMap] using h
    · rw [if_neg hij]
      rw [if_neg hij] at h
      simpa [gen, quotientMap] using h

@[simp] theorem unit_v (i : Fin 2) : unit.v i = gen (sIdx i) := rfl

@[simp] theorem unit_w (i : Fin 2) : unit.w i = gen (tIdx i) := rfl

/-! ## The universal property -/

/-- Evaluation of the presentation at a properly infinite unit. -/
noncomputable def evaluation {A : Type*} [Ring A] (Q : ProperlyInfiniteUnit A) :
    Free →ₐ[ℤ] A :=
  FreeAlgebra.lift ℤ ![Q.v 0, Q.v 1, Q.w 0, Q.w 1]

private theorem evaluation_respects {A : Type*} [Ring A]
    (Q : ProperlyInfiniteUnit A) :
    ∀ {x y : Free}, Relation x y → evaluation Q x = evaluation Q y := by
  intro x y h
  have h00 : Q.w 0 * Q.v 0 = 1 := Q.w_mul_v_self 0
  have h11 : Q.w 1 * Q.v 1 = 1 := Q.w_mul_v_self 1
  have h01 : Q.w 0 * Q.v 1 = 0 := Q.w_mul_v_of_ne (by decide)
  have h10 : Q.w 1 * Q.v 0 = 0 := Q.w_mul_v_of_ne (by decide)
  cases h with
  | delta i j =>
      fin_cases i <;> fin_cases j <;>
        simp [evaluation, sIdx, tIdx, h00, h11, h01, h10]

/-- **The universal property of `𝒞`.**  A properly infinite unit in `A` is the
same thing as a ring map `𝒞 → A`, evaluated at the four generators. -/
noncomputable def lift {A : Type*} [Ring A] (Q : ProperlyInfiniteUnit A) :
    UniversalPairRing →ₐ[ℤ] A :=
  RingQuot.liftAlgHom ℤ ⟨evaluation Q, fun {_ _} h ↦ evaluation_respects Q h⟩

@[simp] theorem lift_gen {A : Type*} [Ring A] (Q : ProperlyInfiniteUnit A)
    (g : Generator) :
    lift Q (gen g) = ![Q.v 0, Q.v 1, Q.w 0, Q.w 1] g := by
  simp [lift, gen, quotientMap, evaluation]

theorem lift_v {A : Type*} [Ring A] (Q : ProperlyInfiniteUnit A) (i : Fin 2) :
    lift Q (unit.v i) = Q.v i := by
  fin_cases i <;> simp [sIdx]

theorem lift_w {A : Type*} [Ring A] (Q : ProperlyInfiniteUnit A) (i : Fin 2) :
    lift Q (unit.w i) = Q.w i := by
  fin_cases i <;> simp [tIdx]

/-! ## The three hypotheses the printed proof needs of `𝒞` -/

/-- `𝒞` is nonzero.  The witness is the binary Leavitt algebra over `𝔽₂`,
whose Leavitt family is in particular a properly infinite unit. -/
instance nontrivial : Nontrivial UniversalPairRing := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  have h10 : (1 : UniversalPairRing) = 0 := Subsingleton.elim _ _
  have himg := congrArg
    (lift (ofLeavittFamily (BinaryLeavitt.family (ZMod 2)))) h10
  rw [map_one, map_zero] at himg
  exact one_ne_zero himg

noncomputable instance countableFree : Countable Free := by
  letI : Countable (FreeMonoid Generator) :=
    Countable.of_equiv (List Generator) (FreeMonoid.ofList (α := Generator))
  letI : Countable (MonoidAlgebra ℤ (FreeMonoid Generator)) :=
    Countable.of_equiv ((FreeMonoid Generator) →₀ ℤ)
      (MonoidAlgebra.coeffEquiv (R := ℤ) (M := FreeMonoid Generator)).symm
  exact Countable.of_equiv (MonoidAlgebra ℤ (FreeMonoid Generator))
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℤ)
      (X := Generator)).symm.toEquiv

noncomputable instance countable : Countable UniversalPairRing :=
  (RingQuot.mkAlgHom_surjective ℤ Relation).countable

instance finiteType : Algebra.FiniteType ℤ UniversalPairRing :=
  Algebra.FiniteType.of_surjective quotientMap
    (RingQuot.mkAlgHom_surjective ℤ Relation)

/-- **`𝒞` is finitely generated as a ring**, which is what the
Ershov--Jaikin-Zapirain theorem asks of it. -/
theorem isFinitelyGeneratedRing : IsFinitelyGeneratedRing UniversalPairRing :=
  (isFinitelyGeneratedRing_iff_finiteType_int UniversalPairRing).mpr finiteType

/-! ## The printed data at `𝒞` -/

/-- The printed `s = s₀`, `t = t₀` of the rank-four computation. -/
noncomputable def pairInverse : OneSidedCompressor.OneSidedInverse UniversalPairRing :=
  unit.toOneSidedInverse

/-- **The printed single fullness witness `t₁ e s₁ = 1`** in `𝒞`. -/
theorem printedFullnessWitness :
    unit.w 1 * pairInverse.e * unit.v 1 = 1 :=
  unit.w_one_mul_e_mul_v_one

end UniversalPair
end GroupApproximation
