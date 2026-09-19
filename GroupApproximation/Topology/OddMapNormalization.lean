import GroupApproximation.Topology.TautologicalAntipodal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Realifying the antipodal residue onto a real sphere

`GroupApproximation.TautologicalAntipodal.AntipodalObstruction` says that on
`ℂ^{N+1} ∖ {0}` there is no continuous, nowhere-vanishing, odd map into `κ → ℂ`
when `Nat.card κ ≤ N`.  A Borsuk--Ulam development delivers the same statement
in *real* coordinates, on the concrete unit sphere

```text
S^d = ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1),
```

in the form "an odd continuous map `S^d → (κ → ℂ)` has a zero as soon as
`2 * Nat.card κ ≤ d`".  This file is the *purely Mathlib* bridge between the
two: it contains no algebraic topology at all, so it compiles and lands
independently of the vendored odd-degree engine.

## The transport

The only geometric content is the linear realification

```text
ℝ^{2N+2} → ℂ^{N+1},  x ↦ (x₀ + i x₁, x₂ + i x₃, …),
```

`realToComplex` below.  It is continuous, odd and injective, and those three
facts are exactly what turns a nowhere-vanishing odd `F` on `ℂ^{N+1} ∖ {0}`
into a nowhere-vanishing odd continuous map on `S^{2N+1}`.  No normalisation
onto a target sphere is needed, because the receiving statement
`SphereComplexCommonZero` already asserts a *zero* rather than a sphere-valued
factorisation.

The numerology is the one recorded in `TautologicalAntipodal`: `Nat.card κ ≤ N`
gives `2 * Nat.card κ ≤ 2N < 2N + 1 = d`, with no slack to spare.  The
degenerate cases need no separate treatment: if `κ` is empty then
`2 * Nat.card κ = 0 ≤ d` still, and the receiving statement produces a zero of a
map into a subsingleton, which is still a contradiction with nowhere-vanishing.

## Main declarations

* `realToComplex` -- the realification `ℝ^{2N+2} → ℂ^{N+1}`, with its
  continuity (`continuous_realToComplex`), oddness (`realToComplex_neg`) and
  injectivity (`eq_zero_of_realToComplex_eq_zero`).
* `antipodalObstruction_of_sphereCommonZero` -- the bridge.  Its hypothesis is
  the real-sphere statement a Borsuk--Ulam development produces, written with no
  reference to any vendored sphere model (literally the unit sphere of
  `EuclideanSpace ℝ (Fin (d + 1))`) and deliberately *not* given a new name:
  it is definitionally `GroupApproximation.STW22.ComplexOddMapCommonZero`, which
  `GroupApproximation/Analysis/STW22AntipodalBlockData.lean` already declares.

Composed with `TautologicalAntipodal.commonZeroProperty_of_antipodalObstruction`
this reduces `TautologicalCommonZero.CommonZeroProperty` to that one statement.
-/

noncomputable section

namespace GroupApproximation
namespace OddMapNormalization

open Metric

/-- The real coordinate carrying the real part of the `i`-th complex
coordinate. -/
def evenIdx (n : ℕ) (i : Fin (n + 1)) : Fin (2 * n + 1 + 1) :=
  ⟨2 * (i : ℕ), by omega⟩

/-- The real coordinate carrying the imaginary part of the `i`-th complex
coordinate. -/
def oddIdx (n : ℕ) (i : Fin (n + 1)) : Fin (2 * n + 1 + 1) :=
  ⟨2 * (i : ℕ) + 1, by omega⟩

/-- The realification `ℝ^{2n+2} → ℂ^{n+1}`, pairing consecutive real
coordinates into one complex coordinate.  It is an `ℝ`-linear isomorphism, but
only continuity, oddness and injectivity are used. -/
def realToComplex (n : ℕ) (x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1))) :
    Fin (n + 1) → ℂ :=
  fun i => (x (evenIdx n i) : ℂ) + (x (oddIdx n i) : ℂ) * Complex.I

theorem continuous_realToComplex (n : ℕ) : Continuous (realToComplex n) := by
  refine continuous_pi fun i => ?_
  have he : Continuous fun x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1)) =>
      x (evenIdx n i) := by fun_prop
  have ho : Continuous fun x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1)) =>
      x (oddIdx n i) := by fun_prop
  have he' : Continuous fun x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1)) =>
      ((x (evenIdx n i) : ℝ) : ℂ) := Complex.continuous_ofReal.comp he
  have ho' : Continuous fun x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1)) =>
      ((x (oddIdx n i) : ℝ) : ℂ) := Complex.continuous_ofReal.comp ho
  exact he'.add (ho'.mul continuous_const)

theorem realToComplex_neg (n : ℕ) (x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1))) :
    realToComplex n (-x) = -realToComplex n x := by
  funext i
  have he : (-x) (evenIdx n i) = -x (evenIdx n i) := rfl
  have ho : (-x) (oddIdx n i) = -x (oddIdx n i) := rfl
  show ((-x) (evenIdx n i) : ℂ) + ((-x) (oddIdx n i) : ℂ) * Complex.I
      = -(((x (evenIdx n i) : ℝ) : ℂ) + ((x (oddIdx n i) : ℝ) : ℂ) * Complex.I)
  rw [he, ho]
  push_cast
  ring

/-- The realification is injective.  This is what keeps the transported map away
from the origin of `ℂ^{n+1}`, and it is the only place where the pairing of
coordinates is used. -/
theorem eq_zero_of_realToComplex_eq_zero (n : ℕ)
    {x : EuclideanSpace ℝ (Fin (2 * n + 1 + 1))} (h : realToComplex n x = 0) :
    x = 0 := by
  have hcoord : ∀ i : Fin (n + 1), x (evenIdx n i) = 0 ∧ x (oddIdx n i) = 0 := by
    intro i
    have hz := congrFun h i
    simp only [realToComplex, Pi.zero_apply] at hz
    exact ⟨by simpa using congrArg Complex.re hz, by simpa using congrArg Complex.im hz⟩
  refine PiLp.ext fun j => ?_
  have hlt : (j : ℕ) / 2 < n + 1 := by omega
  rcases (show (j : ℕ) = 2 * ((j : ℕ) / 2) ∨ (j : ℕ) = 2 * ((j : ℕ) / 2) + 1 by omega) with
    hp | hp
  · have hje : j = evenIdx n ⟨(j : ℕ) / 2, hlt⟩ := by
      apply Fin.val_injective
      show (j : ℕ) = 2 * ((j : ℕ) / 2)
      exact hp
    have h1 := (hcoord ⟨(j : ℕ) / 2, hlt⟩).1
    rw [← hje] at h1
    exact h1
  · have hjo : j = oddIdx n ⟨(j : ℕ) / 2, hlt⟩ := by
      apply Fin.val_injective
      show (j : ℕ) = 2 * ((j : ℕ) / 2) + 1
      exact hp
    have h1 := (hcoord ⟨(j : ℕ) / 2, hlt⟩).2
    rw [← hjo] at h1
    exact h1

/-- **The bridge.**  The real-sphere common-zero statement implies the antipodal
residue of the STW Problem XXII counterexample.

The hypothesis `H` is "an odd continuous map from the unit sphere of `ℝ^{d+1}`
into `κ → ℂ` has a zero as soon as the real dimension `2 * Nat.card κ` of the
target is at most `d`".  It is spelled out inline, in raw Mathlib vocabulary, so
that this file compiles without the vendored odd-degree tree; it is
*definitionally* the already-named `GroupApproximation.STW22.ComplexOddMapCommonZero`
of `GroupApproximation/Analysis/STW22AntipodalBlockData.lean`, whose `Sphere d`
is the abbreviation `↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1)`.
No second name for it is introduced here.

Given `F` continuous, nowhere-vanishing and odd on `ℂ^{N+1} ∖ {0}`, restrict it
along the realification `ℝ^{2N+2} ≅ ℂ^{N+1}` to the unit sphere `S^{2N+1}`.
Injectivity of the realification keeps the composite inside the punctured space,
so it is continuous there; oddness of the realification makes it odd; and
`2 * Nat.card κ ≤ 2N + 1` is exactly the hypothesis of `H`.  The zero it
produces contradicts nowhere-vanishing. -/
theorem antipodalObstruction_of_sphereCommonZero
    (H : ∀ (d : ℕ) (κ : Type) (_ : Finite κ), 2 * Nat.card κ ≤ d →
        ∀ f : C(↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1), κ → ℂ),
          (∀ x, f (-x) = -f x) → ∃ x, f x = 0) :
    TautologicalAntipodal.AntipodalObstruction := by
  intro N κ hfin hcard F hFc hFne hFodd
  have hne : ∀ x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * N + 1 + 1))) 1),
      realToComplex N (x : EuclideanSpace ℝ (Fin (2 * N + 1 + 1))) ≠ 0 :=
    fun x hx => ne_zero_of_mem_unit_sphere x (eq_zero_of_realToComplex_eq_zero N hx)
  have hcont : Continuous
      (F ∘ fun x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * N + 1 + 1))) 1) =>
        realToComplex N (x : EuclideanSpace ℝ (Fin (2 * N + 1 + 1)))) :=
    hFc.comp_continuous ((continuous_realToComplex N).comp continuous_subtype_val)
      fun x => hne x
  have hodd : ∀ x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * N + 1 + 1))) 1),
      F (realToComplex N
            ((-x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * N + 1 + 1))) 1)) :
              EuclideanSpace ℝ (Fin (2 * N + 1 + 1))))
        = -F (realToComplex N (x : EuclideanSpace ℝ (Fin (2 * N + 1 + 1)))) := by
    intro x
    rw [coe_neg_sphere, realToComplex_neg]
    exact hFodd _ (hne x)
  obtain ⟨x, hx⟩ := H (2 * N + 1) κ hfin (by omega) ⟨_, hcont⟩ hodd
  exact hFne _ (hne x) hx

end OddMapNormalization
end GroupApproximation
