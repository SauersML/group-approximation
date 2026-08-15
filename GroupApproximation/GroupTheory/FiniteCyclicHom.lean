import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Homomorphisms out of finite cyclic groups

An element `g` of a group with `g ^ n = 1` induces a homomorphism
`Multiplicative (ZMod n) →* G` sending the additive generator to `g`.
This is the multiplicative face of `ZMod.lift`; the evaluation lemma at
integer casts is what the ping-pong instantiations consume.
-/

namespace GroupApproximation
namespace FiniteCyclicHom

/-- The homomorphism `Multiplicative (ZMod n) →* G` induced by an
element of order dividing `n`. -/
noncomputable def cyclicHom {G : Type*} [Group G] (n : ℕ) (g : G)
    (hg : g ^ n = 1) : Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift n ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      show (n : ℤ) • Additive.ofMul g = 0
      rw [natCast_zsmul, ← ofMul_pow, hg]
      rfl⟩)

theorem cyclicHom_intCast {G : Type*} [Group G] (n : ℕ) (g : G)
    (hg : g ^ n = 1) (k : ℤ) :
    cyclicHom n g hg (Multiplicative.ofAdd ((k : ZMod n))) = g ^ k := by
  unfold cyclicHom
  simp [ZMod.lift_coe, zmultiplesHom_apply, toMul_zsmul]

theorem cyclicHom_one_val {G : Type*} [Group G] (n : ℕ) (g : G)
    (hg : g ^ n = 1) :
    cyclicHom n g hg (Multiplicative.ofAdd ((1 : ℤ) : ZMod n)) = g := by
  rw [cyclicHom_intCast, zpow_one]

end FiniteCyclicHom
end GroupApproximation
