import GroupApproximation.Topology.TautologicalCommonZero

/-!
# The common-zero property in Borsuk--Ulam vocabulary

`GroupApproximation.Topology.TautologicalCommonZero.CommonZeroProperty` is the
Chern-class input of the STW Problem XXII counterexample, and only its rank-one
case is proved (in `TautologicalLineWinding`).  This file restates the residue
in *antipodal* form, which is strictly weaker-looking and is the shape a
Borsuk--Ulam development actually delivers.

## Why this restatement

Degree `-1` homogeneity at the single scalar `c = -1` says exactly

```text
f (-z) = - f z,
```

so a nowhere-vanishing section of `L^{⊕κ}` is in particular a nowhere-vanishing
*odd* map on `ℂ^{N+1} ∖ {0}`.  Normalising and restricting to the unit sphere
turns that into an odd map `S^{2N+1} → S^{2·card κ - 1}`, and real
Borsuk--Ulam forbids it exactly when `2·card κ - 1 < 2N + 1`, i.e. when
`card κ ≤ N` -- precisely the bound in `CommonZeroProperty`.  That numerical
coincidence is the reason this file exists: it says the Chern-class route and
the Borsuk--Ulam route need the *same* hypothesis, with no slack.

`AntipodalObstruction` below is that statement with the spheres removed, so it
can be stated and consumed without any real-coordinate transport.  Supplying
the transport to `Metric.sphere (0 : EuclideanSpace ℝ (Fin (2N+2))) 1` is a
separate, purely mechanical job; it is deliberately not done here, because it
is only worth paying for once an odd-degree theorem exists to receive it.

## Status of the receiving end

`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/` vendors the
foundations of exactly this argument (singular homology and its homotopy
invariance, barycentric subdivision, the `RP^n` cohomology ring model, the
antipodal map and `IsOddMap`).  It is complete as far as it goes -- no
unproved declarations -- but it does **not** yet contain
the degree theorem: `Antipodal.lean` refers to a `Degree.lean` that has not
been ported, and its `IsOddMap` is defined only for self-maps `C(Sphere n,
Sphere n)`.  So the engine is not available today, and nothing in this file
claims otherwise.

## Main results

* `toFun_neg` -- homogeneity at `-1` is antipodality.
* `AntipodalObstruction` -- the Borsuk--Ulam shaped residue.
* `commonZeroProperty_of_antipodalObstruction` -- it implies
  `CommonZeroProperty`.  This is the whole point: a future lane that proves a
  Borsuk--Ulam statement discharges the Chern input without ever mentioning
  Chern classes.
* `not_antipodalObstruction_succ` -- the rank bound is sharp here too, by the
  same `ℂP⁰` witness.
-/

namespace GroupApproximation
namespace TautologicalAntipodal

open TautologicalCommonZero

/-- Degree `-1` homogeneity, read at the single scalar `c = -1`, is exactly
antipodality of the section in homogeneous coordinates. -/
theorem toFun_neg {N : ℕ} {κ : Type*} (f : TautSection N κ)
    {z : Fin (N + 1) → ℂ} (hz : z ≠ 0) :
    f.toFun (-z) = -f.toFun z := by
  have hne1 : (-1 : ℂ) ≠ 0 := by norm_num
  have hsmul : ((-1 : ℂ)) • z = -z := by rw [neg_smul, one_smul]
  have h := f.homogeneous (-1) z hne1 hz
  rw [hsmul] at h
  rw [h]
  simp

/-- **The residue in Borsuk--Ulam form.**  On `ℂ^{N+1} ∖ {0}` there is no
continuous, nowhere-vanishing, odd map into `κ → ℂ` when `card κ ≤ N`.

Normalising such a map and restricting it to the unit sphere gives an odd map
`S^{2N+1} → S^{2·card κ - 1}`, which real Borsuk--Ulam forbids precisely under
this bound; the sphere transport is deliberately left out of the statement.

Both hypotheses are load-bearing.  `Finite κ` cannot be read off the
cardinality bound -- `Nat.card` is `0` for infinite `κ`, while padding a
nowhere-zero odd map into `κ → ℂ` with zeros produces one into a larger index
type.  And the bound itself is sharp: see `not_antipodalObstruction_succ`. -/
def AntipodalObstruction : Prop :=
  ∀ (N : ℕ) (κ : Type) (_ : Finite κ), Nat.card κ ≤ N →
    ∀ F : (Fin (N + 1) → ℂ) → κ → ℂ,
      ContinuousOn F (punctured N) →
      (∀ z : Fin (N + 1) → ℂ, z ≠ 0 → F z ≠ 0) →
      (∀ z : Fin (N + 1) → ℂ, z ≠ 0 → F (-z) = -F z) →
      False

/-- **The reduction.**  A Borsuk--Ulam statement discharges the Chern-class
input of the STW Problem XXII counterexample.

Everything downstream -- the direct-sum regrouping
`TautologicalCommonZero.hasCommonZero_iff_join`, the family form
`hasCommonZero_of_le`, and the bridge to the matrix compression in
`GroupApproximation.Analysis.ChernCommonZeroBridge` -- is already proved, so
this single implication is the entire remaining gap. -/
theorem commonZeroProperty_of_antipodalObstruction
    (h : AntipodalObstruction) : CommonZeroProperty := by
  intro N κ hfin hcard f
  by_contra hcon
  refine h N κ hfin hcard f.toFun f.continuousOn_toFun ?_ ?_
  · intro z hz hzero
    exact hcon ⟨z, hz, hzero⟩
  · intro z hz
    exact toFun_neg f hz

/-- The rank bound in `AntipodalObstruction` is sharp: `z ↦ (z 0)⁻¹` over
`ℂP⁰` is continuous, nowhere vanishing and odd, so relaxing `Nat.card κ ≤ N`
to `Nat.card κ ≤ N + 1` makes the statement false.  This is the same witness
that refutes the relaxed `CommonZeroProperty`. -/
theorem not_antipodalObstruction_succ :
    ¬ ∀ (N : ℕ) (κ : Type) (_ : Finite κ), Nat.card κ ≤ N + 1 →
        ∀ F : (Fin (N + 1) → ℂ) → κ → ℂ,
          ContinuousOn F (punctured N) →
          (∀ z : Fin (N + 1) → ℂ, z ≠ 0 → F z ≠ 0) →
          (∀ z : Fin (N + 1) → ℂ, z ≠ 0 → F (-z) = -F z) →
          False := by
  intro h
  refine h 0 (Fin 1) inferInstance (Nat.card_fin 1).le unitSection.toFun
    unitSection.continuousOn_toFun (fun _ hz => unitSection_ne_zero hz) ?_
  intro z hz
  exact toFun_neg unitSection hz

end TautologicalAntipodal
end GroupApproximation
