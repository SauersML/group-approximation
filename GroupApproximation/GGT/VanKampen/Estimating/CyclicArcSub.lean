import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Sub-arcs of a cyclic arc

`CyclicArc.sub arc i l h` is the arc of length `l` that starts `i` darts into `arc`.  Its darts are
the darts of `arc` after the first `i`, cut to length `l` (`CyclicArc.sub_darts`).
`CyclicArc.shorten` (`Estimating/OsinPocketGapArcs.lean`) is the case `i = 0`.

## Manuscript status

Infrastructure for Osin's Lemma 9.7 (arXiv:math/0411039v3, §9) through the pocket glue modules;
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe v

namespace CyclicArc

/-- The arc of length `l` that starts `i` darts into `arc`. -/
def sub {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (i l : ℕ)
    (h : i + l ≤ arc.length) : CyclicArc cycle where
  start := ⟨(arc.start.1 + i) % cycle.length, by
    rcases Nat.eq_zero_or_pos cycle.length with h0 | hpos
    · have hs := arc.start.2
      have hl := arc.length_le
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    · exact Nat.lt_succ_of_lt (Nat.mod_lt _ hpos)⟩
  length := l
  length_le := by
    have hl := arc.length_le
    omega

/-- A sub-arc starts `i` positions after the arc, modulo the carrier length. -/
theorem sub_start {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (i l : ℕ)
    (h : i + l ≤ arc.length) : (arc.sub i l h).start.1 = (arc.start.1 + i) % cycle.length :=
  rfl

/-- A sub-arc has the requested length. -/
theorem sub_length {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (i l : ℕ)
    (h : i + l ≤ arc.length) : (arc.sub i l h).length = l :=
  rfl

/-- The carrier rotated to a sub-arc is the carrier rotated to the arc, rotated `i` further. -/
theorem sub_rotated {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (i l : ℕ)
    (h : i + l ≤ arc.length) : (arc.sub i l h).rotated = arc.rotated.rotate i := by
  rw [(arc.sub i l h).rotated_eq_rotate, arc.rotated_eq_rotate, List.rotate_rotate, sub_start,
    List.rotate_mod]

/-- The darts of a sub-arc are the darts of the arc after the first `i`, cut to length `l`. -/
theorem sub_darts {Dart : Type v} {cycle : List Dart} (arc : CyclicArc cycle) (i l : ℕ)
    (h : i + l ≤ arc.length) : (arc.sub i l h).darts = (arc.darts.drop i).take l := by
  have hl := arc.length_le
  have hn := arc.rotated_length
  have hi : i ≤ arc.rotated.length := by omega
  have hd : l ≤ (arc.rotated.drop i).length := by
    rw [List.length_drop]
    omega
  show (arc.sub i l h).rotated.take l = ((arc.rotated.take arc.length).drop i).take l
  rw [sub_rotated, List.rotate_eq_drop_append_take hi, List.take_append_of_le_length hd,
    List.drop_take, List.take_take, Nat.min_eq_left (show l ≤ arc.length - i by omega)]

end CyclicArc

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.sub
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.sub_start
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.sub_length
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.sub_rotated
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.sub_darts

end GroupApproximation.GGT.VanKampen.Embedded
