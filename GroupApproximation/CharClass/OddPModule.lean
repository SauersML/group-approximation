import GroupApproximation.CharClass.OddPGroupRing
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.RingHom

/-!
# From an automorphism of order `p` to a module over the group ring

`CartanGroupRing.lean`'s `moduleOfInvolution` turns an `F₂`-linear involution of
a vector space into a module structure over `(ZMod 2)[ℤ/2]`, with the generator
acting as the involution.  This file is the odd-primary twin: an `F_p`-linear
automorphism `τ` with `τ ^ p = 1` makes `V` a module over `(ZMod p)[ℤ/p]`.

Downstream, `τ` is always the cyclic permutation of the slots of an `r`-tuple of
singular simplices, carrying its Koszul sign; `τ ^ r = 1` holds there for *every*
`r`, with no primality hypothesis, because the accumulated sign is
`(-1)^{k² − Σ n_j²}` and `x² ≡ x (mod 2)`.

The construction is the mod-2 one with `if toAdd a = 0 then 1 else τ` replaced by
`τ ^ (toAdd a).val`.  The multiplicativity of that assignment is where `τ ^ p = 1`
is spent, and it is spent through `pow_mod_of_pow_card_eq_one` rather than
through a case analysis, because `ZMod.val_add` reduces addition of residues to
addition of naturals followed by one `% p`.
-/

namespace GroupApproximation.CharClass

/-- If `τ ^ p = 1` then powers of `τ` only see the exponent mod `p`. -/
theorem pow_mod_of_pow_card_eq_one {M : Type*} [Monoid M] {τ : M} {p : ℕ}
    (hτ : τ ^ p = 1) (x : ℕ) : τ ^ (x % p) = τ ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x p]
  rw [pow_add, pow_mul, hτ, one_pow, one_mul]

variable {p : ℕ} [NeZero p] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

/-- The monoid homomorphism out of `ℤ/p` sending the generator to a given
`F_p`-linear automorphism of order dividing `p`. -/
noncomputable def galEndP (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    Multiplicative (ZMod p) →* Module.End (ZMod p) V where
  toFun a := τ ^ (Multiplicative.toAdd a).val
  map_one' := by
    rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, pow_mod_of_pow_card_eq_one hτ, pow_add]

@[simp] theorem galEndP_ofAdd_one (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    galEndP τ hτ (Multiplicative.ofAdd (1 : ZMod p)) = τ ^ ((1 : ZMod p)).val := rfl

/-- The algebra homomorphism `(ZMod p)[ℤ/p] →ₐ[ZMod p] Module.End (ZMod p) V`
extending `galEndP`. -/
noncomputable def galAlgHomP (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    GroupRingZMod p →ₐ[ZMod p] Module.End (ZMod p) V :=
  MonoidAlgebra.lift (ZMod p) (Module.End (ZMod p) V) (Multiplicative (ZMod p))
    (galEndP τ hτ)

/-- **The module-structure bridge.**  An `F_p`-linear automorphism of order
dividing `p` makes `V` a module over the mod-`p` group ring of `ℤ/p`, with the
generator acting as that automorphism. -/
noncomputable abbrev moduleOfOrderP (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    Module (GroupRingZMod p) V :=
  Module.compHom V (galAlgHomP τ hτ).toRingHom

/-- The generator of the group ring acts, under `moduleOfOrderP`, as `τ` —
provided `p ≠ 1`, so that `(1 : ZMod p).val = 1`. -/
theorem moduleOfOrderP_smul (hp : 1 < p) (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1)
    (v : V) :
    letI := moduleOfOrderP τ hτ
    grGen p • v = τ v := by
  letI := moduleOfOrderP τ hτ
  show (galAlgHomP τ hτ (grGen p)) v = τ v
  unfold galAlgHomP grGen
  rw [MonoidAlgebra.lift_single, one_smul]
  show (τ ^ ((1 : ZMod p)).val) v = τ v
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp, pow_one]

end GroupApproximation.CharClass
