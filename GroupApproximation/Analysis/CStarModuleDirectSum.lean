import GroupApproximation.Analysis.CStarHilbertModuleNorm

/-!
# Direct sums of Hilbert C⋆-modules

Two constructions, both unconditional: the **binary direct sum** `E ⊞ F` and
the **finite direct sum** `⨁ i, E i` over a `Fintype`.  In both the inner
product is the sum of the inner products, which is why they belong here rather
than with the definition: a sum of positive elements is positive, and a sum of
positive elements vanishes only if each does, and both of those are statements
about the *order* of `B`, supplied by `Analysis.CStarPositiveOrder`.

## Why these are needed

Three separate downstream users, and each needs a different one of them.

* `KK`-theory adds Kasparov modules by taking the direct sum of the underlying
  Hilbert modules; that is the binary construction, and it is what makes
  `KK(A,B)` a *monoid* before it is anything else.
* The standard module `H_B = ℓ²(B)` is the completion of the finite direct
  sums `B^S`; the Cauchy--Schwarz inequality *in `B^S`* is what proves that
  the cross terms `∑ ⟨xᵢ, yᵢ⟩` of two square-summable sequences converge,
  which is the whole content of "`H_B` has an inner product".
* Kasparov's stabilization theorem is a statement about `H_B ⊕ E`.

## What is proved

The two modules, with all ten axioms discharged, and the projection lemmas
(`prod_inner`, `pi_inner`, and the actions) that later files rewrite with.
Definiteness in the `Fintype` case is `Finset.sum_eq_zero_iff_of_nonneg`, which
is where positivity of each summand is genuinely used --- with no order on `B`
the vanishing of a sum would say nothing about the summands, and the direct sum
would fail to be a Hilbert module.
-/

namespace GroupApproximation
namespace HilbertModule

open OrderZero

universe v w w' u

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [StarOrderedRing B]

/-! ## The binary direct sum -/

/-- **The direct sum of two Hilbert C⋆-modules**, with
`⟨(x₁,x₂), (y₁,y₂)⟩ = ⟨x₁,y₁⟩ + ⟨x₂,y₂⟩`. -/
def prod (E : CStarModule.{v, w} B) (F : CStarModule.{v, w'} B) :
    CStarModule.{v, max w w'} B where
  carrier := E.carrier × F.carrier
  act p b := (E.act p.1 b, F.act p.2 b)
  inner p q := E.inner p.1 q.1 + F.inner p.2 q.2
  act_add_left p q b :=
    Prod.ext (E.act_add_left p.1 q.1 b) (F.act_add_left p.2 q.2 b)
  act_add_right p b c :=
    Prod.ext (E.act_add_right p.1 b c) (F.act_add_right p.2 b c)
  act_assoc p b c := Prod.ext (E.act_assoc p.1 b c) (F.act_assoc p.2 b c)
  act_smul c p b := Prod.ext (E.act_smul c p.1 b) (F.act_smul c p.2 b)
  inner_add_right p q r := by
    show E.inner p.1 (q.1 + r.1) + F.inner p.2 (q.2 + r.2)
        = (E.inner p.1 q.1 + F.inner p.2 q.2)
          + (E.inner p.1 r.1 + F.inner p.2 r.2)
    rw [E.inner_add_right, F.inner_add_right]
    abel
  inner_smul_right c p q := by
    show E.inner p.1 (c • q.1) + F.inner p.2 (c • q.2)
        = c • (E.inner p.1 q.1 + F.inner p.2 q.2)
    rw [E.inner_smul_right, F.inner_smul_right, smul_add]
  inner_act_right p q b := by
    show E.inner p.1 (E.act q.1 b) + F.inner p.2 (F.act q.2 b)
        = (E.inner p.1 q.1 + F.inner p.2 q.2) * b
    rw [E.inner_act_right, F.inner_act_right, add_mul]
  inner_star p q := by
    show star (E.inner p.1 q.1 + F.inner p.2 q.2)
        = E.inner q.1 p.1 + F.inner q.2 p.2
    rw [star_add, E.inner_star, F.inner_star]
  inner_self_isPositive p :=
    (E.inner_self_isPositive p.1).add (F.inner_self_isPositive p.2)
  inner_self_eq_zero p hp := by
    have h1 : (0 : B) ≤ E.inner p.1 p.1 := E.inner_self_nonneg p.1
    have h2 : (0 : B) ≤ F.inner p.2 p.2 := F.inner_self_nonneg p.2
    have h := (add_eq_zero_iff_of_nonneg h1 h2).mp hp
    exact Prod.ext (E.inner_self_eq_zero p.1 h.1) (F.inner_self_eq_zero p.2 h.2)

@[simp] theorem prod_inner (E : CStarModule.{v, w} B)
    (F : CStarModule.{v, w'} B) (p q : E.carrier × F.carrier) :
    (prod E F).inner p q = E.inner p.1 q.1 + F.inner p.2 q.2 := rfl

@[simp] theorem prod_act (E : CStarModule.{v, w} B)
    (F : CStarModule.{v, w'} B) (p : E.carrier × F.carrier) (b : B) :
    (prod E F).act p b = (E.act p.1 b, F.act p.2 b) := rfl

/-! ## Finite direct sums -/

/-- **The direct sum of a finite family of Hilbert C⋆-modules**, with
`⟨x, y⟩ = ∑ᵢ ⟨xᵢ, yᵢ⟩`.

For `E i = B` this is `Bⁿ`, the module in which the partial sums of a
square-summable sequence live, and the Cauchy--Schwarz inequality proved there
is what makes `H_B` an inner-product module. -/
def pi {ι : Type u} [Fintype ι] (E : ι → CStarModule.{v, w} B) :
    CStarModule.{v, max u w} B where
  carrier := ∀ i, (E i).carrier
  act x b := fun i => (E i).act (x i) b
  inner x y := ∑ i, (E i).inner (x i) (y i)
  act_add_left x y b := by
    funext i
    exact (E i).act_add_left (x i) (y i) b
  act_add_right x b c := by
    funext i
    exact (E i).act_add_right (x i) b c
  act_assoc x b c := by
    funext i
    exact (E i).act_assoc (x i) b c
  act_smul c x b := by
    funext i
    exact (E i).act_smul c (x i) b
  inner_add_right x y z := by
    show (∑ i, (E i).inner (x i) (y i + z i))
        = (∑ i, (E i).inner (x i) (y i)) + ∑ i, (E i).inner (x i) (z i)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ =>
      (E i).inner_add_right (x i) (y i) (z i)
  inner_smul_right c x y := by
    show (∑ i, (E i).inner (x i) (c • y i))
        = c • ∑ i, (E i).inner (x i) (y i)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      (E i).inner_smul_right c (x i) (y i)
  inner_act_right x y b := by
    show (∑ i, (E i).inner (x i) ((E i).act (y i) b))
        = (∑ i, (E i).inner (x i) (y i)) * b
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ =>
      (E i).inner_act_right (x i) (y i) b
  inner_star x y := by
    show star (∑ i, (E i).inner (x i) (y i))
        = ∑ i, (E i).inner (y i) (x i)
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => (E i).inner_star (x i) (y i)
  inner_self_isPositive x :=
    OrderZero.isPositiveElem_of_nonneg
      (Finset.sum_nonneg fun i _ => (E i).inner_self_nonneg (x i))
  inner_self_eq_zero x hx := by
    have hnn : ∀ i ∈ (Finset.univ : Finset ι),
        (0 : B) ≤ (E i).inner (x i) (x i) :=
      fun i _ => (E i).inner_self_nonneg (x i)
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hx
    funext i
    exact (E i).inner_self_eq_zero (x i) (h i (Finset.mem_univ i))

@[simp] theorem pi_inner {ι : Type u} [Fintype ι] (E : ι → CStarModule.{v, w} B)
    (x y : ∀ i, (E i).carrier) :
    (pi E).inner x y = ∑ i, (E i).inner (x i) (y i) := rfl

@[simp] theorem pi_act {ι : Type u} [Fintype ι] (E : ι → CStarModule.{v, w} B)
    (x : ∀ i, (E i).carrier) (b : B) :
    (pi E).act x b = fun i => (E i).act (x i) b := rfl

/-- The finite direct sum of copies of `B`, i.e. `Bⁿ` --- the module the
partial sums of a square-summable sequence live in. -/
abbrev piSelf (ι : Type u) [Fintype ι] (B : Type v) [NonUnitalCStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] : CStarModule.{v, max u v} B :=
  pi (fun _ : ι => selfModule B)

@[simp] theorem piSelf_inner {ι : Type u} [Fintype ι] (x y : ι → B) :
    (piSelf ι B).inner x y = ∑ i, star (x i) * y i := rfl

end HilbertModule
end GroupApproximation
