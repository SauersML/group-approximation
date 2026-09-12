import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-! # Retain the base position and length of an actual cyclic arc under a dart map -/

namespace GroupApproximation.GGT.VanKampen.Embedded.CyclicArc

universe u v
variable {A : Type u} {B : Type v} {cycle : List A}

def map (arc : CyclicArc cycle) (f : A → B) : CyclicArc (cycle.map f) where
  start := ⟨arc.start.val, by simpa only [List.length_map] using arc.start.isLt⟩
  length := arc.length
  length_le := by simpa only [List.length_map] using arc.length_le

theorem map_rotated (arc : CyclicArc cycle) (f : A → B) :
    (arc.map f).rotated = arc.rotated.map f := by
  simp only [rotated, map, List.map_append, List.map_drop, List.map_take]

theorem map_darts (arc : CyclicArc cycle) (f : A → B) :
    (arc.map f).darts = arc.darts.map f := by
  change (arc.map f).rotated.take arc.length = (arc.rotated.take arc.length).map f
  rw [map_rotated, List.map_take]

def mapTo (arc : CyclicArc cycle) (f : A → B) {target : List B}
    (h : target = cycle.map f) : CyclicArc target := h.symm ▸ arc.map f

theorem mapTo_start (arc : CyclicArc cycle) (f : A → B) {target : List B}
    (h : target = cycle.map f) : (arc.mapTo f h).start.val = arc.start.val := by
  subst target
  rfl

theorem mapTo_length (arc : CyclicArc cycle) (f : A → B) {target : List B}
    (h : target = cycle.map f) : (arc.mapTo f h).length = arc.length := by
  subst target
  rfl

theorem mapTo_rotated (arc : CyclicArc cycle) (f : A → B) {target : List B}
    (h : target = cycle.map f) : (arc.mapTo f h).rotated = arc.rotated.map f := by
  subst target
  exact arc.map_rotated f

theorem mapTo_darts (arc : CyclicArc cycle) (f : A → B) {target : List B}
    (h : target = cycle.map f) : (arc.mapTo f h).darts = arc.darts.map f := by
  subst target
  exact arc.map_darts f

end GroupApproximation.GGT.VanKampen.Embedded.CyclicArc

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.mapTo_rotated
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.mapTo_darts
