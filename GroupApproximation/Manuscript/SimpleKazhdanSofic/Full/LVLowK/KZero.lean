import GroupApproximation.Leavitt.LeavittModuleRank
import GroupApproximation.Leavitt.UniversalLeavittOver
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.PUnit
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Algebraic `K₀` and the vanishing of the class `[L]` for `L = L(1,2)`

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2, "Infinite finitely presented
simple Kazhdan groups exist"). The repository reaches Q2 through `E₅(L_{𝔽₂}(1,2))`, and the
remaining input is `K₂(4, L) = ⊥` (Khanh, arXiv:2609.08428, Thm 5.1). That proof uses the
Ara-Brustenga-Cortiñas computation `K_*(L(1,2)) = 0` in low degrees. This file covers degree
zero.

`KTheory/K0Basic` in the repository is the *operator* `K₀`, built from star projections, so it
does not apply to the `𝔽₂`-algebra `L`. Here we define the algebraic model:

* `FGProj R`: a finitely generated projective left `R`-module, bundled in the universe of `R`;
* `AlgVMonoid R`: its isomorphism classes, a commutative monoid under direct sum;
* `AlgKZero R := Algebra.GrothendieckAddGroup (AlgVMonoid R)`: the algebraic `K₀(R)`;
* `AlgKZero.cls P`: the class `[P]`.

The main results:

* `AlgKZero.cls_regular_eq_zero`: for any ring with a binary Leavitt family (so `R ≅ R ⊕ R` as
  left modules, `LeavittFamily.linearEquivSquare`), `[R] = 0` in `K₀(R)`;
* `AlgKZero.cls_pow_eq_zero`: `[Rⁿ] = 0` for every `n`;
* `AlgKZero.cls_sum_regular`: `[P ⊕ R] = [P]`;
* `AlgKZero.exists_eq_cls_sub_cls`, `AlgKZero.eq_zero_iff_forall_cls`: every element of `K₀` is a
  difference `[P] - [Q]`, so `K₀(R) = 0` exactly when every class `[P]` vanishes;
* specializations to `L = L_k(1,2)` over any field: `binaryLeavitt_cls_regular_eq_zero` and
  `binaryLeavitt_cls_pow_eq_zero`.

The full vanishing `K₀(L(1,2)) = 0` also needs Bergman's computation `V(L(1,2)) = {0, [L]}`
(Ara-Goodearl-Pardo, K-Theory 26 (2002), Thm 4.3; Bergman, Trans. AMS 200 (1974)), i.e. every
nonzero f.g. projective `L`-module is isomorphic to `L`. With `eq_zero_iff_forall_cls` and
`cls_regular_eq_zero`, that is the only remaining input.
-/

namespace GroupApproximation.Full.LVLowK

universe u

/-- A finitely generated projective left `R`-module, bundled in the universe of `R`
(`simple_kazhdan_sofic_group.tex` l.733-735, the objects of algebraic `K₀`). -/
structure FGProj (R : Type u) [Ring R] : Type (u + 1) where
  /-- The underlying type of the module. -/
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module R carrier]
  [isFinite : Module.Finite R carrier]
  [isProjective : Module.Projective R carrier]

attribute [instance] FGProj.isAddCommGroup FGProj.isModule FGProj.isFinite FGProj.isProjective

namespace FGProj

variable {R : Type u} [Ring R]

/-- Two bundled modules are related when they are isomorphic as left `R`-modules. -/
abbrev Iso (P Q : FGProj R) : Prop :=
  Nonempty (P.carrier ≃ₗ[R] Q.carrier)

/-- The direct sum `P ⊕ Q`, realized as the product module. -/
def sum (P Q : FGProj R) : FGProj R :=
  ⟨P.carrier × Q.carrier⟩

/-- The zero module. -/
def zero : FGProj R :=
  ⟨PUnit.{u + 1}⟩

/-- The left regular module `R`. -/
def regular (R : Type u) [Ring R] : FGProj R :=
  ⟨R⟩

/-- The free module `Rⁿ`, built as the iterated direct sum `(⋯(0 ⊕ R) ⊕ ⋯) ⊕ R`. -/
def pow (R : Type u) [Ring R] : ℕ → FGProj R
  | 0 => zero
  | n + 1 => (pow R n).sum (regular R)

end FGProj

/-- **The monoid `V(R)`**: isomorphism classes of finitely generated projective left
`R`-modules. -/
abbrev AlgVMonoid (R : Type u) [Ring R] : Type (u + 1) :=
  Quot (FGProj.Iso (R := R))

namespace AlgVMonoid

variable {R : Type u} [Ring R]

/-- The isomorphism class of a finitely generated projective module. -/
def mk (P : FGProj R) : AlgVMonoid R :=
  Quot.mk FGProj.Iso P

/-- Isomorphic modules have the same class. -/
theorem mk_eq_mk {P Q : FGProj R} (e : P.carrier ≃ₗ[R] Q.carrier) : mk P = mk Q := by
  show Quot.mk FGProj.Iso P = Quot.mk FGProj.Iso Q
  exact Quot.sound (Nonempty.intro e)

/-- The class of `P ⊕ Q` only depends on the class of `Q`. -/
private def addLeft (P : FGProj R) : AlgVMonoid R → AlgVMonoid R :=
  Quot.lift (fun Q : FGProj R => mk (P.sum Q)) (by
    intro Q Q' h
    obtain ⟨e⟩ := h
    show mk (P.sum Q) = mk (P.sum Q')
    exact mk_eq_mk (P := P.sum Q) (Q := P.sum Q') ((LinearEquiv.refl R P.carrier).prodCongr e))

/-- Addition on `V(R)`: the direct sum. -/
private def add : AlgVMonoid R → AlgVMonoid R → AlgVMonoid R :=
  Quot.lift (fun P : FGProj R => addLeft P) (by
    intro P P' h
    obtain ⟨e⟩ := h
    funext y
    induction y using Quot.ind with
    | mk Q =>
      show mk (P.sum Q) = mk (P'.sum Q)
      exact mk_eq_mk (P := P.sum Q) (Q := P'.sum Q) (e.prodCongr (LinearEquiv.refl R Q.carrier)))

instance : Add (AlgVMonoid R) :=
  ⟨add⟩

instance : Zero (AlgVMonoid R) :=
  ⟨mk FGProj.zero⟩

theorem mk_add_mk (P Q : FGProj R) : mk P + mk Q = mk (P.sum Q) :=
  rfl

theorem mk_zero : mk (FGProj.zero (R := R)) = 0 :=
  rfl

theorem mk_add_assoc (P Q T : FGProj R) :
    mk P + mk Q + mk T = mk P + (mk Q + mk T) := by
  show mk ((P.sum Q).sum T) = mk (P.sum (Q.sum T))
  exact mk_eq_mk (P := (P.sum Q).sum T) (Q := P.sum (Q.sum T))
    (LinearEquiv.prodAssoc R P.carrier Q.carrier T.carrier)

theorem zero_add_mk (P : FGProj R) : 0 + mk P = mk P := by
  show mk ((FGProj.zero (R := R)).sum P) = mk P
  exact mk_eq_mk (P := (FGProj.zero (R := R)).sum P) (Q := P)
    (LinearEquiv.uniqueProd (R := R) (M := P.carrier) (M₂ := PUnit.{u + 1}))

theorem mk_add_zero (P : FGProj R) : mk P + 0 = mk P := by
  show mk (P.sum (FGProj.zero (R := R))) = mk P
  exact mk_eq_mk (P := P.sum (FGProj.zero (R := R))) (Q := P)
    (LinearEquiv.prodUnique (R := R) (M := P.carrier) (M₂ := PUnit.{u + 1}))

theorem mk_add_comm (P Q : FGProj R) : mk P + mk Q = mk Q + mk P := by
  show mk (P.sum Q) = mk (Q.sum P)
  exact mk_eq_mk (P := P.sum Q) (Q := Q.sum P) (LinearEquiv.prodComm R P.carrier Q.carrier)

instance : AddCommMonoid (AlgVMonoid R) where
  add_assoc a b c := by
    induction a using Quot.ind with
    | mk P =>
      induction b using Quot.ind with
      | mk Q =>
        induction c using Quot.ind with
        | mk T => exact mk_add_assoc P Q T
  zero_add a := by
    induction a using Quot.ind with
    | mk P => exact zero_add_mk P
  add_zero a := by
    induction a using Quot.ind with
    | mk P => exact mk_add_zero P
  add_comm a b := by
    induction a using Quot.ind with
    | mk P =>
      induction b using Quot.ind with
      | mk Q => exact mk_add_comm P Q
  nsmul := nsmulRec

/-- **`R ≅ R ⊕ R` in `V(R)`**: over a ring with a binary Leavitt family,
`[R] + [R] = [R]` in the monoid `V(R)`. -/
theorem mk_regular_add_mk_regular (L : LeavittFamily R) :
    mk (FGProj.regular R) + mk (FGProj.regular R) = mk (FGProj.regular R) := by
  show mk ((FGProj.regular R).sum (FGProj.regular R)) = mk (FGProj.regular R)
  exact mk_eq_mk (P := (FGProj.regular R).sum (FGProj.regular R)) (Q := FGProj.regular R)
    L.linearEquivSquare.symm

end AlgVMonoid

/-- **Algebraic `K₀(R)`**: the Grothendieck group of `V(R)`
(`simple_kazhdan_sofic_group.tex` l.733-735; Khanh arXiv:2609.08428, Thm 5.1, input
`K₀(L) = 0` from Ara-Brustenga-Cortiñas). -/
abbrev AlgKZero (R : Type u) [Ring R] : Type (u + 1) :=
  Algebra.GrothendieckAddGroup (AlgVMonoid R)

namespace AlgKZero

variable {R : Type u} [Ring R]

/-- The class `[P] ∈ K₀(R)` of a finitely generated projective module. -/
def cls (P : FGProj R) : AlgKZero R :=
  Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk P)

theorem cls_eq_cls {P Q : FGProj R} (e : P.carrier ≃ₗ[R] Q.carrier) : cls P = cls Q := by
  show Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk P) =
    Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk Q)
  rw [AlgVMonoid.mk_eq_mk e]

/-- `[P ⊕ Q] = [P] + [Q]`. -/
theorem cls_sum (P Q : FGProj R) : cls (P.sum Q) = cls P + cls Q := by
  show Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk (P.sum Q)) =
    Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk P) +
      Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk Q)
  exact map_add Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk P) (AlgVMonoid.mk Q)

/-- `[0] = 0`. -/
theorem cls_zero : cls (FGProj.zero (R := R)) = 0 := by
  show Algebra.GrothendieckAddGroup.of (AlgVMonoid.mk (FGProj.zero (R := R))) = 0
  rw [AlgVMonoid.mk_zero, map_zero]

/-- Every element of `K₀(R)` is a difference of classes `[P] - [Q]`. -/
theorem exists_eq_cls_sub_cls (z : AlgKZero R) : ∃ P Q : FGProj R, z = cls P - cls Q := by
  obtain ⟨⟨a, b⟩, h⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (AlgVMonoid R))).surj z
  obtain ⟨P, rfl⟩ := Quot.exists_rep a
  obtain ⟨Q, hQ⟩ := Quot.exists_rep (b : AlgVMonoid R)
  refine ⟨P, Q, eq_sub_of_add_eq ?_⟩
  show z + Algebra.GrothendieckAddGroup.of (Quot.mk FGProj.Iso Q) =
    Algebra.GrothendieckAddGroup.of (Quot.mk FGProj.Iso P)
  rw [hQ]
  exact h

/-- **`K₀(R) = 0` is equivalent to the vanishing of every class `[P]`.** -/
theorem eq_zero_iff_forall_cls :
    (∀ z : AlgKZero R, z = 0) ↔ ∀ P : FGProj R, cls P = 0 := by
  constructor
  · intro h P
    exact h (cls P)
  · intro h z
    obtain ⟨P, Q, rfl⟩ := exists_eq_cls_sub_cls z
    rw [h P, h Q, sub_zero]

section Leavitt

variable (L : LeavittFamily R)

include L in
/-- **`[R] = 0` in `K₀(R)` for a ring with a binary Leavitt family**: `R ≅ R ⊕ R` as left
modules gives `[R] + [R] = [R]`, and `K₀(R)` is a group
(`simple_kazhdan_sofic_group.tex` l.733-735; Khanh arXiv:2609.08428, Thm 5.1). -/
theorem cls_regular_eq_zero : cls (FGProj.regular R) = 0 := by
  have h : cls (FGProj.regular R) + cls (FGProj.regular R) =
      cls (FGProj.regular R) + 0 := by
    rw [← cls_sum, add_zero]
    exact cls_eq_cls (P := (FGProj.regular R).sum (FGProj.regular R)) (Q := FGProj.regular R)
      L.linearEquivSquare.symm
  exact add_left_cancel h

include L in
/-- `[P ⊕ R] = [P]` in `K₀(R)` for a ring with a binary Leavitt family. -/
theorem cls_sum_regular (P : FGProj R) : cls (P.sum (FGProj.regular R)) = cls P := by
  rw [cls_sum, cls_regular_eq_zero L, add_zero]

include L in
/-- **`[Rⁿ] = 0` in `K₀(R)`** for every `n`, over a ring with a binary Leavitt family. -/
theorem cls_pow_eq_zero (n : ℕ) : cls (FGProj.pow R n) = 0 := by
  induction n with
  | zero => exact cls_zero
  | succ n ih =>
    show cls ((FGProj.pow R n).sum (FGProj.regular R)) = 0
    rw [cls_sum_regular L, ih]

end Leavitt

end AlgKZero

section BinaryLeavitt

variable (k : Type) [Field k]

/-- **`[L] = 0` in `K₀(L)` for `L = L_k(1,2)`**, over every field `k`, in particular for
`k = 𝔽₂` (`simple_kazhdan_sofic_group.tex` l.733-735; Khanh arXiv:2609.08428, Thm 5.1). -/
theorem binaryLeavitt_cls_regular_eq_zero :
    AlgKZero.cls (FGProj.regular (BinaryLeavitt.BinaryLeavittAlgebra k)) = 0 :=
  AlgKZero.cls_regular_eq_zero (BinaryLeavitt.family k)

/-- `[Lⁿ] = 0` in `K₀(L)` for `L = L_k(1,2)` and every `n`. -/
theorem binaryLeavitt_cls_pow_eq_zero (n : ℕ) :
    AlgKZero.cls (FGProj.pow (BinaryLeavitt.BinaryLeavittAlgebra k) n) = 0 :=
  AlgKZero.cls_pow_eq_zero (BinaryLeavitt.family k) n

end BinaryLeavitt

end GroupApproximation.Full.LVLowK
