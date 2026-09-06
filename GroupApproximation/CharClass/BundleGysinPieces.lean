import GroupApproximation.CharClass.BundlePairs

/-!
# Complex vector bundles in the projection model, XXI: the two pieces of the
Gysin cover

`P(p ⊕ 1)` is covered by the affine chart, where the last coordinate is nonzero,
and by the complement of the zero section, where the fibre part is nonzero.  A
Gysin argument needs the homotopy type of each piece and of their intersection.
All three are already in this lane, but stated about the flat subtypes of
`X × Matrix` rather than about subsets of `Proj p.plusOne`, which is the form a
cover produces.  This file supplies the flattening and the three consequences.

* the chart is `E(p)`, which scales to its zero section, so it is the base;
* the complement of the zero section retracts to `P(p)`;
* their intersection is `E(p) ∖ 0`, which normalizes to the sphere bundle.

Nothing here is a new homotopy: `totalHomotopyEquivBase`,
`notZeroHomotopyEquivProj` and `puncturedHomotopyEquivSphere` do the work, and
the content added is the identification of the subtypes.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section GysinPieces

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### The two pieces, as subsets of `P(p ⊕ 1)` -/

/-- The affine chart, as a subset of `P(p ⊕ 1)`. -/
def chartOpensSet (p : Bundle X ι) : Set (Proj p.plusOne) :=
  {z | betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0}

/-- The complement of the zero section, as a subset of `P(p ⊕ 1)`. -/
def notZeroOpensSet (p : Bundle X ι) : Set (Proj p.plusOne) :=
  {z | zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0}

/-- Flattening the chart's double subtype. -/
def chartHomeoOpens (p : Bundle X ι) : Chart p ≃ₜ ↥(chartOpensSet p) where
  toFun z := ⟨⟨(z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ), z.2.1⟩, z.2.2⟩
  invFun z := ⟨((z : Proj p.plusOne) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ),
    (z : Proj p.plusOne).2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Flattening the complement's double subtype. -/
def notZeroHomeoOpens (p : Bundle X ι) : NotZero p ≃ₜ ↥(notZeroOpensSet p) where
  toFun z := ⟨⟨(z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ), z.2.1⟩, z.2.2⟩
  invFun z := ⟨((z : Proj p.plusOne) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ),
    (z : Proj p.plusOne).2, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- **The affine chart is homotopy equivalent to the base.** -/
noncomputable def chartOpensHomotopyEquivBase (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv (↥(chartOpensSet p)) X :=
  ((chartHomeoOpens p).symm.toHomotopyEquiv.trans
      (totalHomeoChart p).symm.toHomotopyEquiv).trans (totalHomotopyEquivBase p)

/-- **The complement of the zero section is homotopy equivalent to `P(p)`.**
Note the target: it is `P(p)`, the hyperplane at infinity, not the base. -/
noncomputable def notZeroOpensHomotopyEquivProj (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv (↥(notZeroOpensSet p)) (Proj p) :=
  (notZeroHomeoOpens p).symm.toHomotopyEquiv.trans (notZeroHomotopyEquivProj p)

/-! ### The intersection is the sphere bundle -/

/-- The intersection of the two pieces, flattened. -/
def interSet (p : Bundle X ι) : Set (X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) :=
  {z | z ∈ projSet p.plusOne ∧ betaEntry z ≠ 0 ∧ zTrace z ≠ 0}

theorem interSet_subset_chartSet (p : Bundle X ι) : interSet p ⊆ chartSet p :=
  fun _ hz => ⟨hz.1, hz.2.1⟩

/-- Flattening the intersection's double subtype. -/
def interHomeoOpens (p : Bundle X ι) :
    ↥(interSet p) ≃ₜ ↥(chartOpensSet p ∩ notZeroOpensSet p) where
  toFun z := ⟨⟨(z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ), z.2.1⟩, z.2.2.1, z.2.2.2⟩
  invFun z := ⟨((z : Proj p.plusOne) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ),
    (z : Proj p.plusOne).2, z.2.1, z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- **The intersection is `E(p) ∖ 0`.**  The affine chart carries the punctured
total space onto the part of the chart missing the zero section, which is
`chartOf_mem_notZeroSet_iff`. -/
noncomputable def puncturedHomeoInter (p : Bundle X ι) : Punctured p ≃ₜ ↥(interSet p) where
  toFun v :=
    ⟨(chartOf p (Set.inclusion (puncturedSet_subset_totalSet p) v)
        : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ),
      (chartOf p (Set.inclusion (puncturedSet_subset_totalSet p) v)).2.1,
      (chartOf p (Set.inclusion (puncturedSet_subset_totalSet p) v)).2.2,
      ((chartOf_mem_notZeroSet_iff p
        (Set.inclusion (puncturedSet_subset_totalSet p) v)).mpr v.2.2).2⟩
  invFun z :=
    ⟨(totalOf p (Set.inclusion (interSet_subset_chartSet p) z) : X × (ι → ℂ)),
      (totalOf p (Set.inclusion (interSet_subset_chartSet p) z)).2,
      by
        refine (chartOf_mem_notZeroSet_iff p
          (totalOf p (Set.inclusion (interSet_subset_chartSet p) z))).mp ?_
        rw [chartOf_totalOf]
        exact ⟨z.2.1, z.2.2.2⟩⟩
  left_inv v := by
    have h := totalOf_chartOf p (Set.inclusion (puncturedSet_subset_totalSet p) v)
    exact Subtype.ext (congrArg (fun w : Total p => (w : X × (ι → ℂ))) h)
  right_inv z := by
    have h := chartOf_totalOf p (Set.inclusion (interSet_subset_chartSet p) z)
    exact Subtype.ext
      (congrArg (fun c : Chart p => (c : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)) h)
  continuous_toFun :=
    (continuous_subtype_val.comp
      ((chartOf p).continuous.comp
        (continuous_inclusion (puncturedSet_subset_totalSet p)))).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.comp
      ((totalOf p).continuous.comp
        (continuous_inclusion (interSet_subset_chartSet p)))).subtype_mk _

/-- **The intersection of the Gysin cover is the sphere bundle of `p`.** -/
noncomputable def interHomotopyEquivSphere (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv (↥(chartOpensSet p ∩ notZeroOpensSet p)) (Sphere p) :=
  ((interHomeoOpens p).symm.toHomotopyEquiv.trans
      (puncturedHomeoInter p).symm.toHomotopyEquiv).trans (puncturedHomotopyEquivSphere p)

end GysinPieces

end Bundle

end CharClass
end GroupApproximation
