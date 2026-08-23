import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Finite-dimensional sterility of the marked compression commutator

The finite-dimensional core of the non-MF theorem
(`non_mf_groups_exist.tex`, Theorem B).  Suppose a group `H` contains a
subset `Γ`, elements `t, c`, and `a ∈ Γ` with

* `t γ t⁻¹ ∈ Γ` for every `γ ∈ Γ` (one-sided compression), and
* `c γ = γ c` for every `γ ∈ Γ` (a lamp commuting with `Γ`).

Then **every** finite-dimensional linear representation of `H`, over
**every** field, kills the marked word

  `w = ⁅t c t⁻¹, a (t c t⁻¹) a⁻¹⁆`.

Neither property (T), nor unitarity, nor centrality of `w` is consumed.
The argument: the commutant of `π(Γ)` inside `End(V)` is carried *into*
itself by conjugation by `π(t)` — one-sided compression transports
commutants one way — and a finite-dimensional subspace contained in an
isomorphic image of itself equals that image
(`Submodule.eq_of_le_of_finrank_le`).  Hence `π(t c t⁻¹)` lands back in
the commutant, commutes with `π(a)`, and the commutator dies.

This is the `End(V)`-commutant analogue of `fixedSubmodule_map_eq` in
`GroupApproximation.Criterion.ExactCompression`, and it calibrates the
manuscript's corona theorem: for the explicit finitely presented group
`E` built there, `w ≠ 1` (witnessed by an infinite Clifford model), so
`E` has no faithful finite-dimensional representation and no finite
quotient can certify `w ≠ 1`.  Property (T) enters only the corona
upgrade, where the Kazhdan projection replaces the dimension count used
here.
-/

namespace GroupApproximation

open Module

open scoped commutatorElement

variable {k V H : Type*} [Field k] [AddCommGroup V] [Module k V] [Group H]

/-- The commutant of the image of a set `Γ` of group elements under a
monoid homomorphism into the endomorphism algebra, as a submodule of
`Module.End k V`.  For a subgroup `Γ`, apply with the coercion
`(Γ : Set H)`. -/
def repCommutant (π : H →* Module.End k V) (Γ : Set H) :
    Submodule k (Module.End k V) where
  carrier := {x | ∀ γ ∈ Γ, π γ * x = x * π γ}
  zero_mem' := by
    intro γ _
    rw [mul_zero, zero_mul]
  add_mem' := by
    intro x y hx hy γ hγ
    rw [mul_add, add_mul, hx γ hγ, hy γ hγ]
  smul_mem' := by
    intro r x hx γ hγ
    rw [mul_smul_comm, smul_mul_assoc, hx γ hγ]

@[simp] theorem mem_repCommutant {π : H →* Module.End k V} {Γ : Set H}
    {x : Module.End k V} :
    x ∈ repCommutant π Γ ↔ ∀ γ ∈ Γ, π γ * x = x * π γ := Iff.rfl

/-- Two-sided multiplication `x ↦ u * x * v`, as a linear endomorphism of
the endomorphism algebra.  With `v` a two-sided inverse of `u` this is
conjugation. -/
def sandwich (u v : Module.End k V) :
    Module.End k V →ₗ[k] Module.End k V where
  toFun x := u * x * v
  map_add' := by
    intro x y
    rw [mul_add, add_mul]
  map_smul' := by
    intro r x
    rw [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]

@[simp] theorem sandwich_apply (u v x : Module.End k V) :
    sandwich u v x = u * x * v := rfl

/-- **A one-sided compression acts onto the finite-dimensional commutant.**
If `t Γ t⁻¹ ⊆ Γ`, conjugation by `π(t)` maps the commutant of `π(Γ)` onto
itself in every finite-dimensional representation.  The inclusion is the
compression relation; equality is the finite-dimensional rank pin. -/
theorem repCommutant_eq_map_sandwich_of_compression [FiniteDimensional k V]
    (π : H →* Module.End k V) {Γ : Set H} {t : H}
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) :
    repCommutant π Γ =
      (repCommutant π Γ).map (sandwich (π t) (π t⁻¹)) := by
  have hTT : π t * π t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hTinvT : π t⁻¹ * π t = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hπconj : ∀ h : H, π (t * h * t⁻¹) = π t * π h * π t⁻¹ := by
    intro h
    rw [map_mul, map_mul]
  have hres : ∀ x : Module.End k V, π t⁻¹ * (π t * x * π t⁻¹) * π t = x := by
    intro x
    calc π t⁻¹ * (π t * x * π t⁻¹) * π t
        = π t⁻¹ * π t * x * (π t⁻¹ * π t) := by
          simp only [mul_assoc]
      _ = x := by rw [hTinvT, one_mul, mul_one]
  have hinj : Function.Injective (sandwich (π t) (π t⁻¹)) := by
    intro x y hxy
    have h1 : π t⁻¹ * (π t * x * π t⁻¹) * π t
        = π t⁻¹ * (π t * y * π t⁻¹) * π t := by
      rw [← sandwich_apply (π t) (π t⁻¹) x,
        ← sandwich_apply (π t) (π t⁻¹) y, hxy]
    rwa [hres, hres] at h1
  have transport : ∀ g x : Module.End k V,
      π t * g * π t⁻¹ * x = x * (π t * g * π t⁻¹) →
      g * (π t⁻¹ * x * π t) = π t⁻¹ * x * π t * g := by
    intro g x hgx
    have h1 : π t⁻¹ * (π t * g * π t⁻¹ * x) * π t
        = g * (π t⁻¹ * x * π t) := by
      simp only [mul_assoc]
      rw [← mul_assoc (π t⁻¹) (π t), hTinvT, one_mul]
    have h2 : π t⁻¹ * (x * (π t * g * π t⁻¹)) * π t
        = π t⁻¹ * x * π t * g := by
      simp only [mul_assoc]
      rw [hTinvT, mul_one]
    rw [← h1, ← h2, hgx]
  have hle : repCommutant π Γ ≤
      (repCommutant π Γ).map (sandwich (π t) (π t⁻¹)) := by
    intro x hx
    refine ⟨π t⁻¹ * x * π t, fun γ hγ => ?_, ?_⟩
    · have hx' : π t * π γ * π t⁻¹ * x = x * (π t * π γ * π t⁻¹) := by
        have h := hx (t * γ * t⁻¹) (hcomp γ hγ)
        rwa [hπconj γ] at h
      exact transport (π γ) x hx'
    · rw [sandwich_apply]
      calc π t * (π t⁻¹ * x * π t) * π t⁻¹
          = π t * π t⁻¹ * x * (π t * π t⁻¹) := by
            simp only [mul_assoc]
        _ = x := by rw [hTT, one_mul, mul_one]
  have hrank : finrank k ((repCommutant π Γ).map (sandwich (π t) (π t⁻¹)))
      = finrank k (repCommutant π Γ) :=
    ((Submodule.equivMapOfInjective _ hinj _).finrank_eq).symm
  exact Submodule.eq_of_le_of_finrank_le hle (le_of_eq hrank)

/-- **One-step self-copy detector.**  In a finite-dimensional representation,
an element commuting with the compressed copy `t Γ t⁻¹` already commutes with
the parent copy `Γ`.  Equivalently, a proper self-copy cannot occupy strictly
less finite-dimensional operator memory than the parent while remaining
unitarily conjugate to it. -/
theorem mem_repCommutant_of_commutes_compressed [FiniteDimensional k V]
    (π : H →* Module.End k V) {Γ : Set H} {t x : H}
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (hx : ∀ γ ∈ Γ, Commute x (t * γ * t⁻¹)) :
    π x ∈ repCommutant π Γ := by
  have heq := repCommutant_eq_map_sandwich_of_compression π hcomp
  rw [heq]
  refine ⟨π (t⁻¹ * x * t), ?_, ?_⟩
  · intro γ hγ
    have hcomm : γ * (t⁻¹ * x * t) = (t⁻¹ * x * t) * γ := by
      have h := (hx γ hγ).eq
      calc
        γ * (t⁻¹ * x * t) = t⁻¹ * ((t * γ * t⁻¹) * x) * t := by group
        _ = t⁻¹ * (x * (t * γ * t⁻¹)) * t := by rw [← h]
        _ = (t⁻¹ * x * t) * γ := by group
    simpa only [map_mul] using congrArg π hcomm
  · rw [sandwich_apply, map_mul, map_mul]
    group

/-- **Sibling commutator collapse.**  If `p` commutes with the compressed copy
and `q` belongs to the parent copy, every finite-dimensional representation
kills `[p,q]`.  This is the exact algebraic endpoint used by the one-step
self-copy/HNN detector: the sibling packet commutes with the child copy, the
child fills the same finite operator memory as its parent, and the sibling
commutator must vanish. -/
theorem map_commutator_eq_one_of_commutes_compressed [FiniteDimensional k V]
    (π : H →* Module.End k V) {Γ : Set H} {t p q : H} (hq : q ∈ Γ)
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (hp : ∀ γ ∈ Γ, Commute p (t * γ * t⁻¹)) :
    π ⁅p, q⁆ = 1 := by
  have hpC : π p ∈ repCommutant π Γ :=
    mem_repCommutant_of_commutes_compressed π hcomp hp
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr
    (Commute.symm (hpC q hq))

/-- The invertible form of the exact one-step self-copy detector.  Every
finite-dimensional linear representation into `GL(V)` kills the sibling
commutator under the same parent/child hypotheses. -/
theorem map_commutator_eq_one_of_commutes_compressed_units
    [FiniteDimensional k V] (π : H →* (Module.End k V)ˣ)
    {Γ : Set H} {t p q : H} (hq : q ∈ Γ)
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ)
    (hp : ∀ γ ∈ Γ, Commute p (t * γ * t⁻¹)) :
    π ⁅p, q⁆ = 1 := by
  have h := map_commutator_eq_one_of_commutes_compressed
    ((Units.coeHom (Module.End k V)).comp π) hq hcomp hp
  exact Units.ext (by simpa using h)

/-- **Finite-dimensional sterility of the marked compression commutator**
(Theorem B of the non-MF manuscript).  A one-sided compression
`t Γ t⁻¹ ⊆ Γ` together with a lamp `c` commuting with `Γ` forces every
finite-dimensional linear representation `π`, over any field, to kill the
marked commutator `⁅t c t⁻¹, a (t c t⁻¹) a⁻¹⁆` for every `a ∈ Γ`.
Neither property (T) nor unitarity is used: the commutant of `π(Γ)` is
finite-dimensional, is carried into itself by conjugation by `π(t)`, and
is therefore carried onto itself. -/
theorem map_marked_commutator_eq_one [FiniteDimensional k V]
    (π : H →* Module.End k V) {Γ : Set H} {t c a : H} (ha : a ∈ Γ)
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (hcen : ∀ γ ∈ Γ, c * γ = γ * c) :
    π ⁅t * c * t⁻¹, a * (t * c * t⁻¹) * a⁻¹⁆ = 1 := by
  have heq := repCommutant_eq_map_sandwich_of_compression π hcomp
  -- the lamp is in the commutant, so its conjugate is as well
  have hcC : π c ∈ repCommutant π Γ := by
    intro γ hγ
    rw [← map_mul, ← map_mul, hcen γ hγ]
  have hdC : π (t * c * t⁻¹) ∈ repCommutant π Γ := by
    have hφc : π (t * c * t⁻¹) = sandwich (π t) (π t⁻¹) (π c) := by
      rw [sandwich_apply, map_mul, map_mul]
    rw [hφc, heq]
    exact Submodule.mem_map_of_mem hcC
  -- so `a` fixes the conjugated lamp, and the marked commutator dies
  have hda : π a * π (t * c * t⁻¹) = π (t * c * t⁻¹) * π a := hdC a ha
  have hfix : π (a * (t * c * t⁻¹) * a⁻¹) = π (t * c * t⁻¹) := by
    rw [map_mul, map_mul, hda, mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  have hcommute : π (t * c * t⁻¹) * π (a * (t * c * t⁻¹) * a⁻¹)
      = π (a * (t * c * t⁻¹) * a⁻¹) * π (t * c * t⁻¹) := by rw [hfix]
  rw [commutatorElement_def, map_mul, map_mul, map_mul, hcommute,
    mul_assoc (π (a * (t * c * t⁻¹) * a⁻¹)) (π (t * c * t⁻¹)), ← map_mul,
    mul_inv_cancel, map_one, mul_one, ← map_mul, mul_inv_cancel, map_one]

/-- The invertible form: every finite-dimensional representation of `H`
by units of the endomorphism algebra (equivalently, by `GL(V)`) kills the
marked compression commutator. -/
theorem map_marked_commutator_eq_one_units [FiniteDimensional k V]
    (π : H →* (Module.End k V)ˣ) {Γ : Set H} {t c a : H} (ha : a ∈ Γ)
    (hcomp : ∀ γ ∈ Γ, t * γ * t⁻¹ ∈ Γ) (hcen : ∀ γ ∈ Γ, c * γ = γ * c) :
    π ⁅t * c * t⁻¹, a * (t * c * t⁻¹) * a⁻¹⁆ = 1 := by
  have h := map_marked_commutator_eq_one
    ((Units.coeHom (Module.End k V)).comp π) ha hcomp hcen
  exact Units.ext (by simpa using h)

end GroupApproximation
