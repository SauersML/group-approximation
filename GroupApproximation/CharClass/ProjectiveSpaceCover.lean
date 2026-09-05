import GroupApproximation.AlgTop.ComplexProjectiveSphere

/-!
# The Mayer–Vietoris cover of complex projective space

`H^*(ℂP^n; F₂)` is computed by induction on `n` from the two-set open cover

```text
ℂP^{d+1}  =  (affine chart)  ∪  (ℂP^{d+1} ∖ {base point}),
```

whose three pieces are, up to homotopy, a point, `ℂP^d`, and `S^{2d+1}`.  All of
the point-set work behind that sentence is in
`GroupApproximation/AlgTop/ComplexProjective*.lean`, over the same projection
model `CP d` of `Analysis/LIXProjectiveSpaceModel.lean` (rank-one self-adjoint
idempotents in `Matrix (Fin (d+1)) (Fin (d+1)) ℂ`).  This file is the bridge:
it presents that cover as a pair of `TopologicalSpace.Opens` of a `TopCat.{0}`
object, which is the shape the mod-2 Mayer–Vietoris sequence consumes.

## Main declarations

* `CPtop d` — `ℂP^d` as an object of `TopCat.{0}`.
* `chartOpen d`, `punctOpen d` — the two opens, with `chartOpen_sup_punctOpen`
  saying they cover.
* `contractibleSpace_chartOpen` — the chart is contractible.
* `punctOpenHomotopyEquiv` — the punctured space is `ℂP^d`.
* `interSphereHomotopyEquiv` — the intersection is `S^{2d+1}`.
* `subsingleton_CPtop_zero` — the base case: `ℂP^0` is a point.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.AlgTop
open GroupApproximation.AlgTop.CPn

/-- Complex projective `d`-space, as an object of `TopCat.{0}`.  The carrier is
the projection model `CP d`. -/
def CPtop (d : ℕ) : TopCat.{0} := TopCat.of (CP d)

/-- The affine chart `{x : entry x 0 0 ≠ 0}` of `ℂP^{d+1}`, as an open set. -/
def chartOpen (d : ℕ) : Opens (CPtop (d + 1)) :=
  ⟨chartSet (d + 1), isOpen_chartSet⟩

/-- The complement of the base point of `ℂP^{d+1}`, as an open set. -/
def punctOpen (d : ℕ) : Opens (CPtop (d + 1)) :=
  ⟨punctured d, isOpen_punctured⟩

@[simp] theorem coe_chartOpen (d : ℕ) :
    ((chartOpen d : Opens (CPtop (d + 1))) : Set (CP (d + 1))) = chartSet (d + 1) := rfl

@[simp] theorem coe_punctOpen (d : ℕ) :
    ((punctOpen d : Opens (CPtop (d + 1))) : Set (CP (d + 1))) = punctured d := rfl

/-- **The two opens cover.** -/
theorem chartOpen_sup_punctOpen (d : ℕ) : chartOpen d ⊔ punctOpen d = ⊤ := by
  refine Opens.ext ?_
  rw [Opens.coe_sup, Opens.coe_top, coe_chartOpen, coe_punctOpen]
  exact union_eq_univ d

/-- The intersection of the two opens, as a set. -/
theorem coe_chartOpen_inf_punctOpen (d : ℕ) :
    ((chartOpen d ⊓ punctOpen d : Opens (CPtop (d + 1))) : Set (CP (d + 1)))
      = chartSet (d + 1) ∩ {x : CP (d + 1) | x ≠ basePoint (d + 1)} := rfl

/-- **The chart is contractible.**  It is homeomorphic to `ℂ^{d+1}`. -/
theorem contractibleSpace_chartOpen (d : ℕ) : ContractibleSpace ↥(chartOpen d) :=
  contractibleSpace_chartSet (d + 1)

/-- **The punctured projective space is the hyperplane.**  `ℂP^{d+1} ∖ {pt}`
deformation retracts onto `ℂP^d`. -/
def punctOpenHomotopyEquiv (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(punctOpen d) (CPtop d) :=
  punctureHomotopyEquiv d

/-- **The intersection is an odd sphere.**  The chart minus its origin is
`ℂ^{d+1} ∖ {0} ≃ S^{2d+1}`. -/
def interSphereHomotopyEquiv (d : ℕ) :
    ContinuousMap.HomotopyEquiv ↥(chartOpen d ⊓ punctOpen d)
      (TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * (d + 1)))) 1)) :=
  interHomotopyEquivSphere d

/-- **The base case.**  `ℂP^0` is a single point. -/
instance subsingleton_CPtop_zero : Subsingleton ↥(CPtop 0) :=
  subsingleton_CP_zero

instance nonempty_CPtop (d : ℕ) : Nonempty ↥(CPtop d) :=
  CP.instNonempty d

instance compactSpace_CPtop (d : ℕ) : CompactSpace ↥(CPtop d) :=
  CP.instCompactSpace d

end CharClass
end GroupApproximation
