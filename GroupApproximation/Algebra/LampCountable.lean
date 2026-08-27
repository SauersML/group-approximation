import GroupApproximation.Algebra.PermutationalWreath
import Mathlib.Data.Finsupp.Encodable

/-!
# Countability of the lamp group and of the wreath product

A bookkeeping file.  The corona-MF predicates of this repository are stated for
countable groups, so the concrete endpoints need `Countable` for the
permutational wreath product, and that reduces to countability of the lamp
group.

A finitely supported configuration over `X` with values in `K` is the same data
as a `Finsupp` into `Additive K`, whose zero is the identity of `K`; Mathlib
supplies countability for those.
-/

namespace GroupApproximation

universe u v w

variable {K : Type u} [Group K] {X : Type v}

/-- A lamp configuration read as a finitely supported function into the
additive copy of the lamp group. -/
noncomputable def lampToFinsupp (f : Lamp K X) : X →₀ Additive K :=
  Finsupp.onFinset (f.2).toFinset (fun x => Additive.ofMul (f.toFun x)) (by
    intro x hx
    refine (Set.Finite.mem_toFinset _).mpr ?_
    intro hcon
    exact hx (congrArg Additive.ofMul hcon))

@[simp] theorem lampToFinsupp_apply (f : Lamp K X) (x : X) :
    lampToFinsupp f x = Additive.ofMul (f.toFun x) := rfl

theorem lampToFinsupp_injective :
    Function.Injective (lampToFinsupp (K := K) (X := X)) := by
  intro f g h
  refine Subtype.ext (funext fun x => ?_)
  have hx : lampToFinsupp f x = lampToFinsupp g x := by rw [h]
  exact hx

instance additive_countable [Countable K] : Countable (Additive K) :=
  inferInstanceAs (Countable K)

/-- The lamp group over a countable site set with a countable lamp group is
countable. -/
instance lamp_countable [Countable X] [Countable K] : Countable (Lamp K X) :=
  Function.Injective.countable lampToFinsupp_injective

variable {G : Type w} [Group G] [MulAction G X]

/-- The permutational wreath product of countable data is countable. -/
instance wreath_countable [Countable X] [Countable K] [Countable G] :
    Countable (Wreath K G X) :=
  Function.Injective.countable
    (f := fun w : Wreath K G X => (w.left, w.right))
    (fun w₁ w₂ h => by
      refine SemidirectProduct.ext ?_ ?_
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)

end GroupApproximation
