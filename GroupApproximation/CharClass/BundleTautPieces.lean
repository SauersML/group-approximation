import GroupApproximation.CharClass.BundleGysinData

/-!
# Complex vector bundles in the projection model, XXV: the tautological line on
the two Gysin pieces

The two remaining fields of a Gysin datum are the Euler class of the tautological
line restricted to each piece of the cover, and both reduce to a statement about
the line itself.

**On the zero section the line is trivial.**  Pulled back along `zeroSectionProj`
the tautological line of `P(p ⊕ 1)` is the constant line `infPoint`, spanned by
the `Unit` vector, so `lineIso` trivialises it with a constant implementer.

**On the hyperplane at infinity the line is `p`.**  For a rank-one `p` the
projectivisation is the base, and pulling the tautological line back along the
inverse of that homeomorphism returns `p` -- **by `rfl`**, since a point of
`P(p)` carries its own matrix and for rank one that matrix is `p`.

Everything is at an arbitrary index type; nothing specialises to `Fin`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section TautPieces

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### On the zero section the tautological line is trivial -/

omit [DecidableEq ι] in
theorem comap_zeroSectionProj_tautLine_apply (p : Bundle X ι) (x : X) :
    comap (zeroSectionProj p) (tautLine p.plusOne) x = infPoint ι := rfl

omit [DecidableEq ι] in
theorem trace_comap_zeroSectionProj_tautLine (p : Bundle X ι) (x : X) :
    (comap (zeroSectionProj p) (tautLine p.plusOne) x).trace = 1 :=
  trace_rankOneProj (infVec_mem_unitVectors (ι := ι))

omit [DecidableEq ι] in
theorem comap_zeroSectionProj_tautLine_diag (p : Bundle X ι) (x : X) :
    comap (zeroSectionProj p) (tautLine p.plusOne) x (Sum.inr ()) (Sum.inr ()) ≠ 0 := by
  show infPoint ι (Sum.inr ()) (Sum.inr ()) ≠ 0
  rw [infPoint, rankOneProj_apply]
  simp

/-- **On the zero section the tautological line is trivial.**  So the chart's
Euler-class field is the Euler class of a trivial line. -/
noncomputable def tautLineZeroSectionIso (p : Bundle X ι) :
    BundleIso (comap (zeroSectionProj p) (tautLine p.plusOne)) (triv X (Fin 1)) :=
  lineIso (comap (zeroSectionProj p) (tautLine p.plusOne))
    (trace_comap_zeroSectionProj_tautLine p) (Sum.inr ())
    (comap_zeroSectionProj_tautLine_diag p)

/-! ### On the hyperplane at infinity the tautological line is `p` -/

/-- The inverse of `projRankOneHomeo`, as a bundled map. -/
noncomputable def projRankOneSection (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) :
    C(X, Proj p) :=
  ⟨(projRankOneHomeo p hp).symm, (projRankOneHomeo p hp).symm.continuous⟩

omit [DecidableEq ι] in
/-- **Pulling the tautological line back along the section returns `p`**, on the
nose.  A point of `P(p)` carries its own matrix, and for a rank-one `p` that
matrix is `p`. -/
theorem comap_projRankOneSection_tautLine (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) :
    comap (projRankOneSection p hp) (tautLine p) = p := rfl

omit [DecidableEq ι] in
/-- The same as an isomorphism, for a consumer that wants one. -/
noncomputable def tautLineProjRankOneIso (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) :
    BundleIso (comap (projRankOneSection p hp) (tautLine p)) p :=
  BundleIso.refl p

/-! ### The section the retraction inverts -/

/-- **The homotopy inverse of `notZeroOpensHomotopyEquivProj` is
`projInclNotZero`**, read through the flattening.  By `rfl`, so a consumer can
substitute one for the other with no congruence step. -/
theorem notZeroOpensHomotopyEquivProj_invFun (p : Bundle X ι) (z : Proj p) :
    (notZeroOpensHomotopyEquivProj p).invFun z
      = notZeroHomeoOpens p (projInclNotZero p z) := rfl

end TautPieces

end Bundle

end CharClass
end GroupApproximation
