import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantSelect.Untouched
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.Block
import GroupApproximation.GGT.VanKampen.ClosedWalkLobeExcision
import GroupApproximation.Meta.AxiomGuard

/-!
# Pinch decomposition of a closed dart walk into petals

Lane gl-infra-01 (infrastructure).  A closed dart walk `c` whose start vertices repeat has an
innermost lobe `L` (a linear block of `c` that is a closed walk with distinct start vertices);
excising it leaves the closed walk `Z ++ X` (rotated so that it is again a list).  Iterating
gives a list of **petals**: closed dart walks with distinct start vertices whose concatenation
is a permutation of `c` (each petal is a linear block of a rotation of what is left).

* `infraPetal_pinch`: one pinch step, with the length drop.
* `infraPetal_IsDecomp`: petals of `c`.
* `infraPetal_exists_decomp`: every closed dart walk has a (nonempty) petal decomposition.

All PROVED, unconditionally.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists

section Pinch

/-- **One pinch.**  A closed dart walk with a repeated start vertex splits as `X ++ L ++ Z`
with `L` a closed walk with distinct start vertices, and the rest `Z ++ X` again closed; both
are strictly shorter than `c`. -/
theorem infraPetal_pinch {M : CombMap.{v}} {c : List M.Dart} (hc : IsClosedDartWalk M c)
    (hrep : ¬(c.map M.vertexOf).Nodup) :
    ∃ X L Z : List M.Dart, c = X ++ L ++ Z ∧ IsClosedDartWalk M L ∧
      (L.map M.vertexOf).Nodup ∧ IsClosedDartWalk M (Z ++ X) ∧
      L.length < c.length ∧ (Z ++ X).length < c.length := by
  have hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e := by
    obtain ⟨-, h, -⟩ := hc
    exact h
  obtain ⟨X, L, Z, hXLZ, hL, hLnd⟩ :=
    ClosedWalkInnermostLobe.exists_innermost_lobe hchain hrep
  have hXZne : X ++ Z ≠ [] := by
    intro h
    obtain ⟨hX, hZ⟩ := List.append_eq_nil_iff.mp h
    apply hrep
    rw [hXLZ, hX, hZ, List.nil_append, List.append_nil]
    exact hLnd
  have hLne : L ≠ [] := by
    obtain ⟨h, -, -⟩ := hL
    exact h
  have hc' : IsClosedDartWalk M (X ++ L ++ Z) := by
    rw [← hXLZ]
    exact hc
  have hXZ : IsClosedDartWalk M (X ++ Z) :=
    P10RoseLobe.roseLobeFL_isClosedDartWalk_excise (A := X) (B := L) (C := Z) hc' hL hXZne
  have hZX : IsClosedDartWalk M (Z ++ X) := IsClosedDartWalk.append_comm (P := X) (Q := Z) hXZ
  have hlen : c.length = X.length + L.length + Z.length := by
    simp only [hXLZ, List.length_append]
  have h1 : 0 < L.length := List.length_pos_iff.mpr hLne
  have h2 : 0 < (X ++ Z).length := List.length_pos_iff.mpr hXZne
  rw [List.length_append] at h2
  refine ⟨X, L, Z, hXLZ, hL, hLnd, hZX, by omega, ?_⟩
  rw [List.length_append]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_pinch

/-- **Petals of `c`**: a list of closed dart walks with distinct start vertices whose
concatenation is a permutation of `c`. -/
def infraPetal_IsDecomp (M : CombMap.{v}) (c : List M.Dart) (Ps : List (List M.Dart)) :
    Prop :=
  (∀ P ∈ Ps, IsClosedDartWalk M P ∧ (P.map M.vertexOf).Nodup) ∧ Ps.flatten.Perm c

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_IsDecomp

/-- Petal decompositions exist, by strong induction on the length. -/
theorem infraPetal_exists_decomp_aux (M : CombMap.{v}) (n : ℕ) :
    ∀ c : List M.Dart, c.length = n → IsClosedDartWalk M c →
      ∃ Ps : List (List M.Dart), Ps ≠ [] ∧ infraPetal_IsDecomp M c Ps := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hc
    by_cases hnd : (c.map M.vertexOf).Nodup
    · refine ⟨[c], List.cons_ne_nil c [], ?_, List.Perm.of_eq (by simp)⟩
      intro P hP
      rcases List.mem_singleton.mp hP with rfl
      exact ⟨hc, hnd⟩
    · obtain ⟨X, L, Z, hXLZ, hL, hLnd, hZX, -, hlt⟩ := infraPetal_pinch hc hnd
      obtain ⟨Qs, -, hQ, hQp⟩ := ih (Z ++ X).length (by omega) (Z ++ X) rfl hZX
      refine ⟨L :: Qs, List.cons_ne_nil L Qs, ?_, ?_⟩
      · intro P hP
        rcases List.mem_cons.mp hP with rfl | hP'
        · exact ⟨hL, hLnd⟩
        · exact hQ P hP'
      · rw [List.flatten_cons]
        refine (List.Perm.append_left L hQp).trans ?_
        rw [hXLZ, List.append_assoc X L Z, ← List.append_assoc L Z X]
        exact List.perm_append_comm

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_exists_decomp_aux

/-- **Every closed dart walk has a nonempty petal decomposition.** -/
theorem infraPetal_exists_decomp {M : CombMap.{v}} {c : List M.Dart}
    (hc : IsClosedDartWalk M c) :
    ∃ Ps : List (List M.Dart), Ps ≠ [] ∧ infraPetal_IsDecomp M c Ps :=
  infraPetal_exists_decomp_aux M c.length c rfl hc

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove.infraPetal_exists_decomp

end Pinch

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10QuadrantMove
