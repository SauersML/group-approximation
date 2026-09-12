import GroupApproximation.CharClass.AcyclicModelsResolution
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.RingHom

/-!
# The mod-2 group ring of `ℤ/2`, concretely

The Cartan-formula comparison (`Cartan.lean`) is stated over the abstract
`Λ`/`T` of `AcyclicModelsResolution.lean`.  This file supplies the concrete
instance the program wants: `Λ := (ZMod 2)[ℤ/2]`, presented as
`MonoidAlgebra (ZMod 2) (Multiplicative (ZMod 2))`, together with:

* the generator `groupRingGen` and the two facts `AcyclicModelsResolution.lean`
  needs from it (`T*T=1`, `(2:Λ)=0`);
* **the module-structure bridge**: an `F₂`-vector space `V` equipped with an
  `F₂`-linear involution `τ` (the data that actually occurs downstream — a
  swap of tensor factors, or the antipode of the periodic resolution acting on
  a target complex) becomes a `Λ`-module, with the involution acting as the
  generator.  This is the one place the whole equivariant design could fail to
  typecheck, so it is settled here, on its own, before anything is built on
  top of it.

The construction of the module structure: an involution `τ` with `τ*τ = 1` is
a monoid homomorphism `Multiplicative (ZMod 2) →* Module.End (ZMod 2) V`
(`galEnd`, sending the generator to `τ`), which lifts along the universal
property of the group ring (`MonoidAlgebra.lift`) to an algebra homomorphism
`Λ →ₐ[ZMod 2] Module.End (ZMod 2) V`, whose underlying ring homomorphism
turns the *tautological* action of `Module.End (ZMod 2) V` on `V`
(`LinearMap.applyModule`, a Mathlib instance) into the wanted `Module Λ V`
(`Module.compHom`).
-/

namespace GroupApproximation.CharClass

/-- **The mod-2 group ring of `ℤ/2`.** -/
abbrev GroupRingZ2 : Type := MonoidAlgebra (ZMod 2) (Multiplicative (ZMod 2))

/-- The generator `t` of `ℤ/2` inside the group ring. -/
noncomputable def groupRingGen : GroupRingZ2 :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod 2)) (1 : ZMod 2)

/-- `t * t = 1`: the generator is an involution of the group ring. -/
theorem groupRingGen_mul_self : groupRingGen * groupRingGen = 1 := by
  unfold groupRingGen
  rw [MonoidAlgebra.single_mul_single]
  have h1 : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
    rw [← ofAdd_add, ← ofAdd_zero]
    congr 1
  rw [h1, mul_one, ← MonoidAlgebra.one_def]

/-- The group ring has characteristic `2`. -/
theorem two_eq_zero_groupRingZ2 : (2 : GroupRingZ2) = 0 := by
  have h : (2 : GroupRingZ2) = algebraMap (ZMod 2) GroupRingZ2 (2 : ZMod 2) := by
    rw [map_ofNat]
  rw [h, show (2 : ZMod 2) = 0 from by decide, map_zero]

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

/-- The monoid homomorphism out of `ℤ/2` sending the generator to a given
involution `τ`. -/
noncomputable def galEnd (τ : Module.End (ZMod 2) V) (hτ : τ * τ = 1) :
    Multiplicative (ZMod 2) →* Module.End (ZMod 2) V where
  toFun a := if Multiplicative.toAdd a = 0 then 1 else τ
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    have hadd : Multiplicative.toAdd (a * b) = Multiplicative.toAdd a + Multiplicative.toAdd b :=
      toAdd_mul a b
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases zmod2_eq_zero_or_one (Multiplicative.toAdd a) with ha | ha <;>
      rcases zmod2_eq_zero_or_one (Multiplicative.toAdd b) with hb | hb <;>
      rw [hadd, ha, hb] <;>
      simp [hτ, h11]

/-- The algebra homomorphism `Λ →ₐ[ZMod 2] Module.End (ZMod 2) V` extending `galEnd`. -/
noncomputable def galAlgHom (τ : Module.End (ZMod 2) V) (hτ : τ * τ = 1) :
    GroupRingZ2 →ₐ[ZMod 2] Module.End (ZMod 2) V :=
  MonoidAlgebra.lift (ZMod 2) (Module.End (ZMod 2) V) (Multiplicative (ZMod 2)) (galEnd τ hτ)

/-- **The module-structure bridge.**  An `F₂`-linear involution of `V` makes
`V` a module over the mod-2 group ring of `ℤ/2`, with the generator acting as
the involution. -/
noncomputable abbrev moduleOfInvolution (τ : Module.End (ZMod 2) V) (hτ : τ * τ = 1) :
    Module GroupRingZ2 V :=
  Module.compHom V (galAlgHom τ hτ).toRingHom

/-- The generator of the group ring acts, under `moduleOfInvolution`, exactly as
`τ`. -/
theorem moduleOfInvolution_smul (τ : Module.End (ZMod 2) V) (hτ : τ * τ = 1) (v : V) :
    letI := moduleOfInvolution τ hτ
    groupRingGen • v = τ v := by
  letI := moduleOfInvolution τ hτ
  show (galAlgHom τ hτ groupRingGen) v = τ v
  unfold galAlgHom groupRingGen
  rw [MonoidAlgebra.lift_single, one_smul]
  rfl

/-- **The periodic resolution at the concrete group ring.** -/
noncomputable def W : ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ :=
  periodicResolution groupRingGen groupRingGen_mul_self two_eq_zero_groupRingZ2

end GroupApproximation.CharClass
