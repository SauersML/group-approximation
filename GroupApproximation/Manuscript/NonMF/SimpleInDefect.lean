import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.KazhdanCompressionFunctorial
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# The simple factor in every mapped compression defect

This isolated endpoint packages Lemma `lem:simple-in-defect` from
`non_mf_groups_exist.tex` at the `FournierFacioDefectData` interface.

For a datum `D`, the manuscript's subgroups `π(S)` and `Γ` are respectively
`D.simpleSubgroup` and `D.iota.range`.  Thus their images under `ρ` are
`D.simpleSubgroup.map ρ` and `D.iota.range.map ρ`.  The first theorem below is
the marked-core statement requested by the proof: the image of the simple
factor lies in the defect normal subgroup of the mapped core for every
homomorphism.  The remaining theorems identify that marked defect with a
subgroup of the exact one-sided defect printed in the manuscript.

Neither surjectivity nor nontriviality of the mapped simple factor is needed
for the containment.  They are retained in the final wrapper solely so its
hypotheses have exactly the form printed in `lem:simple-in-defect`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF

open scoped commutatorElement

universe u v

variable {P : Type} {E : Type u} {L : Type v}
  [Group P] [Group E] [Group L]

/-- The image of the Fournier--Facio simple factor lies in the defect normal
subgroup of the mapped compression core, for every homomorphism. -/
theorem map_simpleSubgroup_le_defectNormal
    (D : FournierFacioDefectData P E) (rho : E →* L) :
    D.simpleSubgroup.map rho ≤ (D.core.map rho).defectNormal :=
  D.core.map_subgroup_le_defectNormal rho D.simpleSubgroup
    D.simpleSubgroup_le_defectNormal

/-- A marked core's defect normal subgroup is contained in the exact
one-sided compression--centralizer defect printed in the manuscript. -/
theorem defectNormal_le_printedDefect (C : KazhdanCompressionCore P L) :
    C.defectNormal ≤ OneSidedMFRadical.printedDefect C.iota.range := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨p, rfl⟩
  exact OneSidedMFRadical.printedDefect_generator_mem C.iota.range
    C.t_mem_compressionSet C.c_commutes_range ⟨p, rfl⟩

/-- The exact containment asserted by the printed lemma, without its
unnecessary surjectivity and nontrivial-image hypotheses. -/
theorem map_simpleSubgroup_le_printedDefect
    (D : FournierFacioDefectData P E) (rho : E →* L) :
    D.simpleSubgroup.map rho ≤
      OneSidedMFRadical.printedDefect (D.iota.range.map rho) := by
  rw [← MonoidHom.range_comp]
  exact (map_simpleSubgroup_le_defectNormal D rho).trans
    (defectNormal_le_printedDefect (D.core.map rho))

/-- **`lem:simple-in-defect`, in its printed hypothesis shape.**

Here `D.simpleSubgroup.map rho` is `ρ(π(S))` and
`D.iota.range.map rho` is `ρ(Γ)`.  The proof above shows that the two printed
hypotheses are stronger than necessary for this containment. -/
theorem manuscriptLemmaSimpleInDefect
    (D : FournierFacioDefectData P E) (rho : E →* L)
    (_rho_surjective : Function.Surjective rho)
    (_simple_image_ne_bot : D.simpleSubgroup.map rho ≠ ⊥) :
    D.simpleSubgroup.map rho ≤
      OneSidedMFRadical.printedDefect (D.iota.range.map rho) :=
  map_simpleSubgroup_le_printedDefect D rho

end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.manuscriptLemmaSimpleInDefect
