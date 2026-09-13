import GroupApproximation.GGT.SystolicDisc
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# HC6 in two cases

Let `d` be a dart of a triangulated disc with both sides on inner faces, so that `d` and
`alpha d` sit in two triangles `[d, d₁, d₂]` and `[alpha d, e₁, e₂]` whose third vertices carry
the same label.  The fold of HC6 (`MirrorFoldStatement`) splits on whether the two third
vertices are distinct vertices of the disc.

* Distinct (`MirrorFoldDistinctStatement`): deleting the edge of `d` merges the two triangles
  into a quadrilateral; folding its two middle darts leaves a digon, whose edge is deleted.
* Coincident (`MirrorFoldPinchedStatement`): deleting the edge of `d` leaves a face through the
  common third vertex twice; splitting that vertex disconnects the map, and the component of the
  outer face loses a digon.

* `TriangulatedDisc.eq_rotation_of_faceOf_eq`: a dart on an inner face is one of its three
  rotations.
* `TriangulatedDisc.faceOf_alpha_ne_of_inner`: the two sides of an edge of an inner face lie on
  distinct faces, since a triangle of `X` has three distinct vertices.
* `mirrorFoldStatement_of_cases`: HC6 from the two cases.

## Manuscript status

Infrastructure for the torsion-free hyperbolic property (T) witness on the
Kotowski--Ollivier route; certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace Systolic

open GGT.VanKampen

universe u

variable {V : Type u}

namespace TriangulatedDisc

variable {X : TriangleComplex V} {γ : List V} (D : TriangulatedDisc X γ)

/-- **A dart on an inner face is one of its three rotations.** -/
theorem eq_rotation_of_faceOf_eq {d e : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer)
    (he : D.map.faceOf e = D.map.faceOf d) :
    e = d ∨ e = D.map.facePerm d ∨ e = (D.map.facePerm ^ 2) d := by
  obtain ⟨h3, -⟩ := D.tri d hd
  obtain ⟨i, hi⟩ := ((D.map.faceOf_eq_iff e d).mp he).symm.exists_nat_pow_eq
  have hq : (D.map.facePerm ^ (3 * (i / 3))) d = d := by
    rw [pow_mul]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h3 _
  obtain ⟨r, hr, hre⟩ : ∃ r, r < 3 ∧ (D.map.facePerm ^ r) d = e := by
    refine ⟨i % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    rw [← hi]
    conv_rhs => rw [← Nat.mod_add_div i 3, pow_add, Equiv.Perm.mul_apply, hq]
  interval_cases r
  · rw [pow_zero, Equiv.Perm.one_apply] at hre
    exact Or.inl hre.symm
  · rw [pow_one] at hre
    exact Or.inr (Or.inl hre.symm)
  · exact Or.inr (Or.inr hre.symm)

/-- **The two sides of an edge of an inner face lie on distinct faces**: a triangle of `X` has
three distinct vertices, so it never reads an edge twice. -/
theorem faceOf_alpha_ne_of_inner {d : D.map.Dart} (hd : D.map.faceOf d ≠ D.outer) :
    D.map.faceOf (D.map.alpha d) ≠ D.map.faceOf d := by
  intro h
  obtain ⟨-, htri⟩ := D.tri d hd
  obtain ⟨-, h23, h13⟩ := X.tri_adj htri
  rcases D.eq_rotation_of_faceOf_eq hd h with h0 | h1 | h2
  · exact D.map.alpha_fixedPointFree d h0
  · -- `alpha d = facePerm d`: the third dart starts where `d` starts
    have hv : D.map.vertexOf ((D.map.facePerm ^ 2) d) = D.map.vertexOf d := by
      rw [perm_pow_two_apply, ← h1, Systolic.facePerm_alpha, D.map.vertexOf_sigma]
    rw [hv] at h13
    exact X.G.irrefl h13
  · -- `alpha d = (facePerm ^ 2) d`: the second and third darts start at one vertex
    have hv : D.map.vertexOf ((D.map.facePerm ^ 2) d) = D.map.vertexOf (D.map.facePerm d) := by
      rw [← h2, Systolic.vertexOf_facePerm]
    rw [hv] at h23
    exact X.G.irrefl h23

end TriangulatedDisc

section Statements

variable (X : TriangleComplex V)

/-- **HC6, distinct third vertices**: a mirror pair of inner triangles whose third vertices
are distinct vertices of the disc folds away. -/
def MirrorFoldDistinctStatement : Prop :=
  ∀ (γ : List V) (D : TriangulatedDisc X γ) (d : D.map.Dart),
    D.map.faceOf d ≠ D.outer → D.map.faceOf (D.map.alpha d) ≠ D.outer →
    D.vtx (D.third d) = D.vtx (D.third (D.map.alpha d)) →
    D.third d ≠ D.third (D.map.alpha d) →
      ∃ D' : TriangulatedDisc X γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount

/-- **HC6, a common third vertex**: two inner triangles on the two sides of an edge whose
third vertices are one vertex of the disc fold away. -/
def MirrorFoldPinchedStatement : Prop :=
  ∀ (γ : List V) (D : TriangulatedDisc X γ) (d : D.map.Dart),
    D.map.faceOf d ≠ D.outer → D.map.faceOf (D.map.alpha d) ≠ D.outer →
    D.third d = D.third (D.map.alpha d) →
      ∃ D' : TriangulatedDisc X γ, D'.innerFaceCount + 2 ≤ D.innerFaceCount

end Statements

variable {X : TriangleComplex V}

/-- **HC6 from its two cases.** -/
theorem mirrorFoldStatement_of_cases (hdist : MirrorFoldDistinctStatement X)
    (hpinch : MirrorFoldPinchedStatement X) : MirrorFoldStatement X := by
  intro γ D d hd had hlab
  by_cases h : D.third d = D.third (D.map.alpha d)
  · exact hpinch γ D d hd had h
  · exact hdist γ D d hd had hlab h

end Systolic
end GroupApproximation

#audit_axioms GroupApproximation.Systolic.TriangulatedDisc.eq_rotation_of_faceOf_eq
#audit_axioms GroupApproximation.Systolic.TriangulatedDisc.faceOf_alpha_ne_of_inner
#audit_axioms GroupApproximation.Systolic.mirrorFoldStatement_of_cases
