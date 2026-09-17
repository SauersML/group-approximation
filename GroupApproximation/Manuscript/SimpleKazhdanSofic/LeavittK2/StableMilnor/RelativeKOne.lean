import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableMilnor.StableRingMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative `K₁` of a surjective ring map

Lane sk-leavitt-16, third module.  For a ring map `f : R →+* S` (in the application
`f = Ideal.Quotient.mk I`, so `ker f = I`):

* `relativeGL f = GL(R, ker f)`, the kernel of `glColimMap f : GL(R) → GL(S)`;
* `relativeElementaryColim f`, the normal closure **in `GL(R)`** of the stabilized relative
  elementary units `e_{ij}(a)`, `f a = 0`;
* `relativeKOne f = GL(R, ker f) ⧸ E'(R, ker f)` and the forgetful map
  `relativeKOneToKOne f : K₁(R, ker f) → K₁(R)`.

**Convention.**  Milnor (§4) defines `E(R, I)` as the normal closure of the relative elementary
units inside `E(R)`.  His Lemma 4.3 (relative Whitehead lemma) shows it is normal in `GL(R)`,
hence equals the `GL(R)`-normal closure used here; that lemma is *not* formalized in this lane,
so the definition below is the `GL(R)`-normal closure and the identification with Milnor's
`E(R, I)` is only a remark.  The exactness theorem of `Exact.lean` holds for this `K₁(R, I)`
with no appeal to Lemma 4.3.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation GroupApproximation.AlgebraicK

section Relative

variable {R S : Type*} [Ring R] [Ring S]

/-- `GL(R, ker f)`: stable invertible matrices that become trivial modulo `ker f`. -/
noncomputable def relativeGL (f : R →+* S) : Subgroup (ClassicalGLColim R) :=
  (glColimMap f).ker

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeGL

instance relativeGL_normal (f : R →+* S) : (relativeGL f).Normal :=
  MonoidHom.normal_ker (glColimMap f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeGL_normal

/-- The stabilized relative elementary units `e_{ij}(a)` with `f a = 0`. -/
def relativeElementarySet (f : R →+* S) : Set (ClassicalGLColim R) :=
  {g | ∃ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : R),
    f a = 0 ∧ g = glColimOf R n (elementaryUnit i j hij a)}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementarySet

/-- `E'(R, ker f)`: the `GL(R)`-normal closure of the relative elementary units (equal to
Milnor's `E(R, I)` by his Lemma 4.3, not formalized here). -/
noncomputable def relativeElementaryColim (f : R →+* S) : Subgroup (ClassicalGLColim R) :=
  Subgroup.normalClosure (relativeElementarySet f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementaryColim

instance relativeElementaryColim_normal (f : R →+* S) :
    (relativeElementaryColim f).Normal :=
  Subgroup.normalClosure_normal

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementaryColim_normal

theorem glColimOf_elementaryUnit_mem_relativeElementaryColim (f : R →+* S) {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) {a : R} (ha : f a = 0) :
    glColimOf R n (elementaryUnit i j hij a) ∈ relativeElementaryColim f :=
  Subgroup.subset_normalClosure ⟨n, i, j, hij, a, ha, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.glColimOf_elementaryUnit_mem_relativeElementaryColim

/-- `E'(R, ker f) ⊆ GL(R, ker f)`. -/
theorem relativeElementaryColim_le_relativeGL (f : R →+* S) :
    relativeElementaryColim f ≤ relativeGL f := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨n, i, j, hij, a, ha, rfl⟩
  change glColimMap f (glColimOf R n (elementaryUnit i j hij a)) = 1
  rw [glColimMap_glColimOf, elementaryMatrixUnitMap_elementaryUnit, ha, elementaryUnit_zero,
    map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementaryColim_le_relativeGL

/-- `E'(R, ker f) ⊆ E(R)`. -/
theorem relativeElementaryColim_le_elementaryColim (f : R →+* S) :
    relativeElementaryColim f ≤ elementaryColim R := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨n, i, j, hij, a, -, rfl⟩
  exact glColimOf_mem_elementaryColim R (elementaryUnit_mem i j hij a)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementaryColim_le_elementaryColim

instance relativeElementaryColim_subgroupOf_normal (f : R →+* S) :
    ((relativeElementaryColim f).subgroupOf (relativeGL f)).Normal :=
  (relativeElementaryColim_normal f).subgroupOf (relativeGL f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeElementaryColim_subgroupOf_normal

/-- **Relative `K₁`**: `K₁(R, ker f) = GL(R, ker f) ⧸ E'(R, ker f)`. -/
noncomputable abbrev relativeKOne (f : R →+* S) : Type _ :=
  relativeGL f ⧸ (relativeElementaryColim f).subgroupOf (relativeGL f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOne

theorem relativeGL_subtype_le_comap (f : R →+* S) :
    (relativeElementaryColim f).subgroupOf (relativeGL f)
      ≤ (elementaryColim R).comap (relativeGL f).subtype := by
  intro g hg
  rw [Subgroup.mem_comap]
  exact relativeElementaryColim_le_elementaryColim f (Subgroup.mem_subgroupOf.mp hg)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeGL_subtype_le_comap

/-- The forgetful map `K₁(R, ker f) → K₁(R) = GL(R) ⧸ E(R)`. -/
noncomputable def relativeKOneToKOne (f : R →+* S) :
    relativeKOne f →* ClassicalGLColim R ⧸ elementaryColim R :=
  QuotientGroup.map _ (elementaryColim R) (relativeGL f).subtype (relativeGL_subtype_le_comap f)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOneToKOne

theorem relativeKOneToKOne_mk (f : R →+* S) (g : relativeGL f) :
    relativeKOneToKOne f (g : relativeKOne f)
      = ((g : ClassicalGLColim R) : ClassicalGLColim R ⧸ elementaryColim R) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relativeKOneToKOne_mk

end Relative

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
