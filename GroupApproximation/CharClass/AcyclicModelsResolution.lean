import GroupApproximation.CharClass.AcyclicModels
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.LinearCombination

/-!
# The periodic free resolution of `ZMod 2` over a `ℤ/2`-group ring

The `ℤ/2`-equivariant acyclic-models theorem (`AcyclicModels.lean`) is the
ordinary theorem instantiated at `Λ := (ZMod 2)[ℤ/2]`, the group ring; the
Cartan formula compares two natural chain maps out of a functor of the shape
`X ↦ W ⊗ S(X)`, where `W` is the standard periodic free resolution of `ZMod 2`
over that group ring, regarded as a `ChainComplex` concentrated nowhere (it is
a fixed complex, independent of `X`, so as a functor out of any category it is
`(Functor.const _).obj W`).

## The classical resolution, and why it collapses mod 2

Over `ℤ`, the standard free resolution of `ℤ` (with the trivial action) by the
group ring `ℤ[ℤ/2] = ℤ[T]/(T² − 1)` of the cyclic group of order two is

```text
⋯ ⟶ ℤ[ℤ/2] --(1−T)--> ℤ[ℤ/2] --(1+T)--> ℤ[ℤ/2] --(1−T)--> ℤ[ℤ/2] ⟶ ℤ ⟶ 0
```

with the two differentials **alternating**.  Reducing mod `2`, `1 − T` and
`1 + T` are the *same* element (`−1 = 1` in characteristic `2`), so the
alternation collapses and the whole resolution is built from **one** repeated
differential.  This file records exactly that one fact, generically: for any
commutative ring `Λ` of characteristic `2` carrying an "involution" element `T`
(`T * T = 1`), the complex with `Λ` in every degree and differential
`(1 + T) ·` in every step is a chain complex (`d ∘ d = 0` because
`(1+T)² = 1 + 2T + T² = 1 + 0 + 1 = 2 = 0`), and it is termwise free of rank
one over `Λ`.  Whoever instantiates the Cartan comparison supplies their own
concrete `Λ` (a `MonoidAlgebra`, an `AddMonoidAlgebra`, or anything else
presenting the same ring) together with `T` and the two one-line hypotheses;
nothing here commits to a particular presentation.
-/

universe u

namespace GroupApproximation.CharClass

open CategoryTheory

section Periodic

variable {Λ : Type} [CommRing Λ] (T : Λ)

/-- The repeated differential of the periodic resolution: left multiplication
by `1 + T`. -/
noncomputable def periodicDiff : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ :=
  ModuleCat.ofHom (LinearMap.mulLeft Λ (1 + T))

@[simp] theorem periodicDiff_apply (x : Λ) : (periodicDiff T) x = (1 + T) * x := by
  simp [periodicDiff]

/-- **The chain-complex condition**, from `T * T = 1` and characteristic `2`:
`(1+T)² = 1 + 2T + T² = 1 + 0 + 1 = 2 = 0`. -/
theorem periodicDiff_comp_periodicDiff (hT : T * T = 1) (h2 : (2 : Λ) = 0) :
    periodicDiff T ≫ periodicDiff T = 0 := by
  have key : (1 + T) * (1 + T) = 0 := by
    linear_combination hT + (1 + T) * h2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [periodicDiff, ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.zero_apply]
  calc (1 + T) * ((1 + T) * x) = (1 + T) * (1 + T) * x := by ring
    _ = 0 * x := by rw [key]
    _ = 0 := by ring

/-- **The periodic resolution.**  `Λ` in every degree, differential `1 + T` in
every step.  At `Λ := (ZMod 2)[ℤ/2]` with `T` the class of the generator, this
is the standard free resolution of `ZMod 2` by the group ring, reduced mod `2`
so that its two classically-alternating differentials coincide. -/
noncomputable def periodicResolution (hT : T * T = 1) (h2 : (2 : Λ) = 0) :
    ChainComplex (ModuleCat.{0} Λ) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of Λ Λ) (fun _ => periodicDiff T)
    (fun _ => periodicDiff_comp_periodicDiff T hT h2)

@[simp] theorem periodicResolution_X (hT : T * T = 1) (h2 : (2 : Λ) = 0) (k : ℕ) :
    (periodicResolution T hT h2).X k = ModuleCat.of Λ Λ :=
  rfl

@[simp] theorem periodicResolution_d (hT : T * T = 1) (h2 : (2 : Λ) = 0) (k : ℕ) :
    (periodicResolution T hT h2).d (k + 1) k = periodicDiff T := by
  unfold periodicResolution
  exact ChainComplex.of_d (fun _ : ℕ => ModuleCat.of Λ Λ) (fun _ : ℕ => periodicDiff T) k

/-- **Termwise freeness of rank one.**  Every degree of the periodic
resolution is `Λ` itself, so it carries the one-point basis `{1}` — the same
basis as `Module.Basis.singleton Unit Λ`, transported along `periodicResolution_X`
(so `Module.Basis.singleton_apply` computes it: the value at the unique index is
`(1 : Λ)`). -/
noncomputable def periodicResolutionBasis (hT : T * T = 1) (h2 : (2 : Λ) = 0) (k : ℕ) :
    Module.Basis Unit Λ ((periodicResolution T hT h2).X k) :=
  Module.Basis.singleton Unit Λ

end Periodic

end GroupApproximation.CharClass
