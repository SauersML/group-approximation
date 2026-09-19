import GroupApproximation.Algebra.WreathLampPushforward
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.GroupTheory.OrderOfElement

/-!
# Corollary 43.2: what a mod-two lamp remembers

Section 43.2 takes the lamp group `K = C₂`, where abelianization does nothing,
and identifies the invisible radical (43.5) as the *parity-per-height* kernel:
a configuration is invisible exactly when every height fibre carries an even
number of lit lamps.  So the approximation theories retain one bit per occupied
height and forget every even rearrangement inside a fibre -- in sharp contrast
with a perfect lamp, where by `Algebra/PerfectLamp` nothing at all survives.

The radical is the kernel of the height pushforward of Section 37.1, so the
content of Corollary 43.2 item 5 is a computation of that kernel for `C₂`:

* `mem_ker_pushHom_iff` -- membership in the pushforward kernel, fibre by
  fibre, for an arbitrary abelian lamp group;
* `mem_ker_pushHom_modTwo_iff` -- for `C₂` the fibre condition is exactly
  evenness of the number of lit lamps over that fibre, which is (43.5).

The equivalence of items 1--4 of Corollary 43.2 with membership in the radical
is the general theory (`Sofic/ThreeRadicalsCoincide`, `Algebra/VisibleQuotient`)
and is not repeated here; this file supplies the concrete description that
item 5 adds.
-/

namespace GroupApproximation

namespace WreathLampPushforward

universe u v w

variable {K : Type u} [CommGroup K] {X : Type v} {Y : Type w}

/-- Membership in the kernel of the pushforward is a fibrewise condition. -/
theorem mem_ker_pushHom_iff (q : X → Y) (f : Lamp K X) :
    f ∈ (pushHom q).ker ↔ ∀ y : Y, pushFun q f y = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h y
    have h2 : (push q f).toFun y = (1 : Lamp K Y).toFun y :=
      congrArg (fun g : Lamp K Y => g.toFun y) h
    rw [push_apply, Lamp.one_apply] at h2
    exact h2
  · intro h
    refine Lamp.ext fun y => ?_
    rw [Lamp.one_apply]
    show pushFun q f y = 1
    exact h y

/-! ## The mod-two lamp -/

/-- The mod-two lamp group `C₂`, written multiplicatively. -/
abbrev ModTwo : Type := Multiplicative (ZMod 2)

/-- `C₂` has a single nonidentity element. -/
theorem eq_gen_of_ne_one {a : ModTwo} (ha : a ≠ 1) :
    a = Multiplicative.ofAdd (1 : ZMod 2) := by
  have hz : ∀ n : ZMod 2, n ≠ 0 → n = 1 := by decide
  have hne : Multiplicative.toAdd a ≠ 0 := by
    intro hcon
    refine ha (Multiplicative.toAdd.injective ?_)
    simpa using hcon
  refine Multiplicative.toAdd.injective ?_
  simpa using hz _ hne

/-- A power of the generator is trivial exactly for even exponents. -/
theorem gen_pow_eq_one_iff (n : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod 2)) ^ n = 1 ↔ Even n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (Multiplicative.ofAdd (1 : ZMod 2)) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  rw [← orderOf_dvd_iff_pow_eq_one, hord, ← even_iff_two_dvd]

open scoped Classical in
/-- Over a set of lit sites the configuration is constantly the generator, so
its product is a power of the generator. -/
theorem prod_eq_gen_pow (f : Lamp ModTwo X) (S : Finset X) (hS : S ⊆ supp f) :
    ∏ x ∈ S, f.toFun x = (Multiplicative.ofAdd (1 : ZMod 2)) ^ S.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_congr rfl fun x hx => eq_gen_of_ne_one (mem_supp.mp (hS hx))

open scoped Classical in
/-- **Corollary 43.2, item 5.**  For mod-two lamps the pushforward kernel --
that is, the radical (43.5) -- consists of exactly those configurations every
one of whose fibres carries an even number of lit lamps. -/
theorem mem_ker_pushHom_modTwo_iff (q : X → Y) (f : Lamp ModTwo X) :
    f ∈ (pushHom q).ker ↔
      ∀ y : Y, Even ((supp f).filter (fun x => q x = y)).card := by
  rw [mem_ker_pushHom_iff]
  refine forall_congr' fun y => ?_
  have hpush : pushFun q f y
      = ∏ x ∈ (supp f).filter (fun x => q x = y), f.toFun x := rfl
  rw [hpush, prod_eq_gen_pow f _ (Finset.filter_subset _ _), gen_pow_eq_one_iff]

end WreathLampPushforward

end GroupApproximation
