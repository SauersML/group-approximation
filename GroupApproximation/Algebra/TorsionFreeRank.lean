import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Subsingleton
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Torsion-free rank of an abelian group, and of an abelianization

The multiplicity paragraph of the manuscript (`non_mf_groups_exist.tex`,
anchor on "distinct torsion-free ranks") separates the groups `E × ℤ^k` by the
invariant it names there: *the torsion-free rank of the abelianization*.
This file supplies that invariant and the two facts the paragraph uses
about it --- additivity over direct products, and finiteness on finitely
generated groups.

The definition taken here is the standard one: the torsion-free rank of an
abelian group `A` is the `ℚ`-dimension of `ℚ ⊗_ℤ A`.  Tensoring with `ℚ`
is exactly what kills the torsion, and this is checked, not assumed:
`torsionFreeRank_eq_zero_of_forall_zsmul_eq_zero` says that a group all of
whose elements are killed by some nonzero integer has rank `0`.  Together
with `torsionFreeRank_int` (`rk ℤ = 1`) and `torsionFreeRank_prod`
(additivity) this pins the invariant down on finitely generated abelian
groups, where it is the classical torsion-free rank.

Everything about `ℚ`-dimensions is Mathlib's: `Module.rank` over a field,
`rank_prod'` for products of free modules, `Module.rank_lt_aleph0` for
finite modules, and `Module.Finite.base_change` for the passage from a
finitely generated abelian group to a finite-dimensional `ℚ`-vector
space.  The only genuinely new construction is the comparison
`Abelianization (G × H) ≃* Abelianization G × Abelianization H`, which
Mathlib does not have and which the manuscript's step
`(E × ℤ^k)^{ab} ≅ E^{ab} × ℤ^k` needs.

## Main definitions

* `GroupApproximation.TorsionFreeRank.torsionFreeRank`: the torsion-free
  rank of an abelian group, as a cardinal.
* `GroupApproximation.TorsionFreeRank.abelianizationRank`: the torsion-free
  rank of the abelianization of a group.
* `GroupApproximation.TorsionFreeRank.abelianizationProd`: abelianization
  turns a direct product into a direct product.

## Main statements

* `torsionFreeRank_prod`, `abelianizationRank_prod`: additivity.
* `torsionFreeRank_int`, `abelianizationRank_multiplicativeInt`: the rank
  of `ℤ` is `1`.
* `torsionFreeRank_lt_aleph0`, `abelianizationRank_lt_aleph0`: finite
  generation makes the rank finite, which is what lets the invariant
  separate anything at all.
-/

namespace GroupApproximation
namespace TorsionFreeRank

open scoped TensorProduct

universe u

/-! ## The invariant -/

/-- The **torsion-free rank** of an abelian group `A`: the `ℚ`-dimension of
`ℚ ⊗_ℤ A`.  Torsion is annihilated by the tensor factor, so this is the
rank of the free part; see
`torsionFreeRank_eq_zero_of_forall_zsmul_eq_zero`. -/
noncomputable def torsionFreeRank (A : Type u) [AddCommGroup A] : Cardinal.{u} :=
  Module.rank ℚ (ℚ ⊗[ℤ] A)

/-- Unfolding lemma for `torsionFreeRank`. -/
@[simp] theorem torsionFreeRank_eq (A : Type u) [AddCommGroup A] :
    torsionFreeRank A = Module.rank ℚ (ℚ ⊗[ℤ] A) := rfl

/-- Isomorphic abelian groups have the same torsion-free rank: an additive
equivalence is `ℤ`-linear, and base change along `ℤ → ℚ` turns it into a
`ℚ`-linear equivalence. -/
theorem torsionFreeRank_of_addEquiv {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : torsionFreeRank A = torsionFreeRank B :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    e.toIntLinearEquiv).rank_eq

/-! ## Torsion is invisible to the invariant -/

/-- **A torsion group has torsion-free rank zero.**  If `n • a = 0` with
`n ≠ 0` then `q ⊗ a = (n • (q/n)) ⊗ a = (q/n) ⊗ (n • a) = 0`, so the whole
tensor product collapses. -/
theorem torsionFreeRank_eq_zero_of_forall_zsmul_eq_zero {A : Type u} [AddCommGroup A]
    (h : ∀ a : A, ∃ n : ℤ, n ≠ 0 ∧ n • a = 0) : torsionFreeRank A = 0 := by
  have hzero : ∀ x : ℚ ⊗[ℤ] A, x = 0 := by
    intro x
    induction x with
    | zero => rfl
    | tmul q a =>
        obtain ⟨n, hn, hna⟩ := h a
        have hnQ : ((n : ℚ)) ≠ 0 := Int.cast_ne_zero.mpr hn
        have hq : n • (q / (n : ℚ)) = q := by
          rw [zsmul_eq_mul]
          field_simp
        calc q ⊗ₜ[ℤ] a
            = (n • (q / (n : ℚ))) ⊗ₜ[ℤ] a := by rw [hq]
          _ = (q / (n : ℚ)) ⊗ₜ[ℤ] (n • a) := TensorProduct.smul_tmul _ _ _
          _ = (q / (n : ℚ)) ⊗ₜ[ℤ] (0 : A) := by rw [hna]
          _ = 0 := by simp
    | add x y hx hy => rw [hx, hy, add_zero]
  haveI : Subsingleton (ℚ ⊗[ℤ] A) := ⟨fun x y => by rw [hzero x, hzero y]⟩
  show Module.rank ℚ (ℚ ⊗[ℤ] A) = 0
  simp

/-- The trivial group has torsion-free rank zero. -/
theorem torsionFreeRank_eq_zero_of_subsingleton (A : Type u) [AddCommGroup A]
    [Subsingleton A] : torsionFreeRank A = 0 :=
  torsionFreeRank_eq_zero_of_forall_zsmul_eq_zero fun a =>
    ⟨1, one_ne_zero, by rw [one_smul]; exact Subsingleton.elim a 0⟩

/-! ## The two computations the manuscript needs -/

/-- **Additivity of the torsion-free rank over direct products.**  Tensor
products distribute over binary products, and the rank of a product of
`ℚ`-vector spaces is the sum of the ranks. -/
theorem torsionFreeRank_prod (A B : Type u) [AddCommGroup A] [AddCommGroup B] :
    torsionFreeRank (A × B) = torsionFreeRank A + torsionFreeRank B := by
  have e : (ℚ ⊗[ℤ] (A × B)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] A) × (ℚ ⊗[ℤ] B) :=
    TensorProduct.prodRight ℤ ℚ ℚ A B
  calc torsionFreeRank (A × B)
      = Module.rank ℚ (ℚ ⊗[ℤ] (A × B)) := rfl
    _ = Module.rank ℚ ((ℚ ⊗[ℤ] A) × (ℚ ⊗[ℤ] B)) := e.rank_eq
    _ = Module.rank ℚ (ℚ ⊗[ℤ] A) + Module.rank ℚ (ℚ ⊗[ℤ] B) := rank_prod'
    _ = torsionFreeRank A + torsionFreeRank B := rfl

/-- **The torsion-free rank of `ℤ` is `1`.** -/
theorem torsionFreeRank_int : torsionFreeRank ℤ = 1 := by
  calc torsionFreeRank ℤ
      = Module.rank ℚ (ℚ ⊗[ℤ] ℤ) := rfl
    _ = Module.rank ℚ ℚ := (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).rank_eq
    _ = 1 := by simp

/-- **A finitely generated abelian group has finite torsion-free rank.**
Finite generation over `ℤ` base-changes to finite generation over `ℚ`, and
a finite module has rank below `ℵ₀`.  Without this the invariant would
separate nothing: `κ + k = κ + l` carries no information for infinite
`κ`. -/
theorem torsionFreeRank_lt_aleph0 (A : Type u) [AddCommGroup A] [AddGroup.FG A] :
    torsionFreeRank A < Cardinal.aleph0 := by
  haveI : Module.Finite ℤ A := Module.Finite.iff_addGroup_fg.mpr ‹AddGroup.FG A›
  show Module.rank ℚ (ℚ ⊗[ℤ] A) < Cardinal.aleph0
  exact Module.rank_lt_aleph0 ℚ (ℚ ⊗[ℤ] A)

/-! ## Abelianization of a direct product

Mathlib has the abelianization functor but not its compatibility with
binary products, which is `[G × H, G × H] = [G,G] × [H,H]` read as an
isomorphism.  The two maps are the obvious ones. -/

section AbelianizationProd

variable (G H : Type*) [Group G] [Group H]

/-- Abelianizing each coordinate of a product. -/
def abelianizationProdHom :
    Abelianization (G × H) →* Abelianization G × Abelianization H :=
  Abelianization.lift (MonoidHom.prodMap Abelianization.of Abelianization.of)

/-- `abelianizationProdHom` on a class of a pair. -/
@[simp] theorem abelianizationProdHom_of (x : G × H) :
    abelianizationProdHom G H (Abelianization.of x)
      = (Abelianization.of x.1, Abelianization.of x.2) := rfl

/-- Recombining the two coordinate abelianizations.  The target is
commutative, so the two coordinate inclusions have a coproduct. -/
def abelianizationProdInv :
    Abelianization G × Abelianization H →* Abelianization (G × H) :=
  (Abelianization.map (MonoidHom.inl G H)).coprod (Abelianization.map (MonoidHom.inr G H))

/-- `abelianizationProdInv` on a pair of classes. -/
@[simp] theorem abelianizationProdInv_mk (a : Abelianization G) (b : Abelianization H) :
    abelianizationProdInv G H (a, b)
      = Abelianization.map (MonoidHom.inl G H) a
          * Abelianization.map (MonoidHom.inr G H) b := rfl

/-- Recombining after splitting is the identity: `(g,1)·(1,h) = (g,h)`. -/
theorem abelianizationProdInv_comp_hom :
    (abelianizationProdInv G H).comp (abelianizationProdHom G H)
      = MonoidHom.id (Abelianization (G × H)) := by
  refine Abelianization.hom_ext _ _ (MonoidHom.ext ?_)
  intro x
  obtain ⟨g, h⟩ := x
  show abelianizationProdInv G H
      (abelianizationProdHom G H (Abelianization.of ((g, h) : G × H)))
        = Abelianization.of ((g, h) : G × H)
  have hstep : abelianizationProdInv G H
      (abelianizationProdHom G H (Abelianization.of ((g, h) : G × H)))
        = Abelianization.of ((g, 1) : G × H) * Abelianization.of ((1, h) : G × H) := rfl
  have hof : Abelianization.of ((g, 1) : G × H) * Abelianization.of ((1, h) : G × H)
      = Abelianization.of (((g, 1) : G × H) * ((1, h) : G × H)) :=
    (map_mul Abelianization.of _ _).symm
  have hmul : ((g, 1) : G × H) * ((1, h) : G × H) = ((g, h) : G × H) := by simp
  rw [hstep, hof, hmul]

/-- Splitting after recombining is the identity: each inclusion lands in
its own coordinate. -/
theorem abelianizationProdHom_comp_inv :
    (abelianizationProdHom G H).comp (abelianizationProdInv G H)
      = MonoidHom.id (Abelianization G × Abelianization H) := by
  refine MonoidHom.ext ?_
  rintro ⟨⟨a⟩, ⟨b⟩⟩
  show abelianizationProdHom G H
      (abelianizationProdInv G H (Abelianization.of a, Abelianization.of b))
        = (Abelianization.of a, Abelianization.of b)
  have hstep : abelianizationProdInv G H (Abelianization.of a, Abelianization.of b)
      = Abelianization.of ((a, 1) : G × H) * Abelianization.of ((1, b) : G × H) := rfl
  have hmm : abelianizationProdHom G H
      (Abelianization.of ((a, 1) : G × H) * Abelianization.of ((1, b) : G × H))
        = abelianizationProdHom G H (Abelianization.of ((a, 1) : G × H))
            * abelianizationProdHom G H (Abelianization.of ((1, b) : G × H)) :=
    map_mul _ _ _
  rw [hstep, hmm, abelianizationProdHom_of, abelianizationProdHom_of]
  simp

/-- **Abelianization commutes with binary direct products.**  This is the
step `(E × ℤ^k)^{ab} ≅ E^{ab} × ℤ^k` of the manuscript's multiplicity
paragraph. -/
def abelianizationProd :
    Abelianization (G × H) ≃* Abelianization G × Abelianization H where
  toFun := ⇑(abelianizationProdHom G H)
  invFun := ⇑(abelianizationProdInv G H)
  left_inv := DFunLike.congr_fun (abelianizationProdInv_comp_hom G H)
  right_inv := DFunLike.congr_fun (abelianizationProdHom_comp_inv G H)
  map_mul' := map_mul (abelianizationProdHom G H)

end AbelianizationProd

/-! ## Finite generation of an abelianization -/

/-- The canonical map to the abelianization is surjective. -/
theorem abelianization_of_surjective (G : Type u) [Group G] :
    Function.Surjective (Abelianization.of : G →* Abelianization G) := by
  rintro ⟨g⟩
  exact ⟨g, rfl⟩

/-- A finitely generated group has a finitely generated abelianization. -/
theorem abelianization_fg (G : Type u) [Group G] [Group.FG G] :
    Group.FG (Abelianization G) :=
  Group.fg_of_surjective (abelianization_of_surjective G)

/-! ## The invariant of a group -/

/-- The **torsion-free rank of the abelianization** of a group: the
invariant the manuscript uses to separate `E × ℤ^k` from `E × ℤ^l`. -/
noncomputable def abelianizationRank (G : Type u) [Group G] : Cardinal.{u} :=
  torsionFreeRank (Additive (Abelianization G))

/-- Unfolding lemma for `abelianizationRank`. -/
@[simp] theorem abelianizationRank_eq (G : Type u) [Group G] :
    abelianizationRank G = torsionFreeRank (Additive (Abelianization G)) := rfl

/-- Isomorphic groups have abelianizations of the same torsion-free rank.
This is the direction the nonisomorphism argument contraposes. -/
theorem abelianizationRank_congr {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    abelianizationRank G = abelianizationRank H :=
  torsionFreeRank_of_addEquiv (MulEquiv.toAdditive e.abelianizationCongr)

/-- **Additivity of the invariant over direct products.**  Abelianization
turns the product into a product, and the torsion-free rank is additive. -/
theorem abelianizationRank_prod (G H : Type u) [Group G] [Group H] :
    abelianizationRank (G × H) = abelianizationRank G + abelianizationRank H := by
  have e : Additive (Abelianization (G × H)) ≃+
      Additive (Abelianization G) × Additive (Abelianization H) :=
    (MulEquiv.toAdditive (abelianizationProd G H)).trans
      (AddEquiv.prodAdditive (Abelianization G) (Abelianization H))
  calc abelianizationRank (G × H)
      = torsionFreeRank (Additive (Abelianization (G × H))) := rfl
    _ = torsionFreeRank (Additive (Abelianization G) × Additive (Abelianization H)) :=
        torsionFreeRank_of_addEquiv e
    _ = torsionFreeRank (Additive (Abelianization G))
          + torsionFreeRank (Additive (Abelianization H)) := torsionFreeRank_prod _ _
    _ = abelianizationRank G + abelianizationRank H := rfl

/-- The infinite cyclic group contributes `1`. -/
theorem abelianizationRank_multiplicativeInt :
    abelianizationRank (Multiplicative ℤ) = 1 := by
  have e : Additive (Abelianization (Multiplicative ℤ)) ≃+ ℤ :=
    (MulEquiv.toAdditive (Abelianization.equivOfComm (H := Multiplicative ℤ)).symm).trans
      (AddEquiv.additiveMultiplicative ℤ)
  calc abelianizationRank (Multiplicative ℤ)
      = torsionFreeRank (Additive (Abelianization (Multiplicative ℤ))) := rfl
    _ = torsionFreeRank ℤ := torsionFreeRank_of_addEquiv e
    _ = 1 := torsionFreeRank_int

/-- The trivial group contributes `0`. -/
theorem abelianizationRank_eq_zero_of_subsingleton (G : Type u) [Group G]
    [Subsingleton G] : abelianizationRank G = 0 := by
  haveI : Subsingleton (Abelianization G) := (abelianization_of_surjective G).subsingleton
  exact torsionFreeRank_eq_zero_of_subsingleton (Additive (Abelianization G))

/-- **A finitely generated group has an abelianization of finite
torsion-free rank.** -/
theorem abelianizationRank_lt_aleph0 (G : Type u) [Group G] [Group.FG G] :
    abelianizationRank G < Cardinal.aleph0 := by
  haveI : Group.FG (Abelianization G) := abelianization_fg G
  exact torsionFreeRank_lt_aleph0 (Additive (Abelianization G))

end TorsionFreeRank
end GroupApproximation
