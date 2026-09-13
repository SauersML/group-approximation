import Mathlib.Data.List.Rotate
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: face walks on a cell boundary

Manuscript `\label{thm:hull}` (Hull's small cancellation theorem), least-area route through
Osin (math/0411039v3, §9), proof of Lemma 9.4: "The boundary of `Δ̃_i` decomposes into `k_i`
subpaths".  `OsinLemma94ClassPolygons` asks that the darts of a class on a relator cell form a
cyclic arc of that cell's boundary.  The class producer reads such a class as a face walk: a
dart `d` followed by `facePerm d`, `facePerm (facePerm d)`, and so on.  This module shows that a
face walk from a boundary dart is the boundary read from that dart, and that a face walk longer
than the boundary repeats its first dart.

* `FaceBoundary.getElem?_add_mod_length`: `r` steps of `facePerm` move `r` places along the
  boundary, cyclically.
* `FaceBoundary.pow_length_apply`: `facePerm ^ length` fixes every boundary dart.
* `FaceBoundary.rotate_take_eq_map_pow`: the first `m ≤ length` darts of the boundary rotated to
  `j` are the face walk of length `m` from dart `j`.
* `List.eq_map_pow_of_isChain`: a list chained by `p` is the `p`-walk from its head.
* `Embedded.CyclicArc.exists_darts_eq_map_pow`: a face walk of length at most the boundary
  length from a dart of a relator cell is a cyclic arc of that cell.
* `FaceBoundary.two_le_count_map_pow`: a face walk longer than the boundary visits its first
  dart twice.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- `r` steps of `facePerm` from the dart at position `j` of a face boundary reach position
`(j + r) % length`.  Osin math/0411039v3, Lemma 9.4, inside Hull's proof of `thm:hull`: the
boundary of a cell is read cyclically. -/
theorem FaceBoundary.getElem?_add_mod_length {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {j : ℕ} (hj : j < B.darts.length) (r : ℕ) :
    B.darts[(j + r) % B.darts.length]? = some ((M.facePerm ^ r) (B.darts[j]'hj)) := by
  have step : ∀ {k : ℕ} (hk : k < B.darts.length),
      B.darts[(k + 1) % B.darts.length]? = some (M.facePerm (B.darts[k]'hk)) := by
    intro k hk
    by_cases h : k + 1 < B.darts.length
    · rw [Nat.mod_eq_of_lt h, List.getElem?_eq_getElem h]
      exact congrArg some ((List.isChain_iff_getElem.mp B.chain) k h).symm
    · have hmod : (k + 1) % B.darts.length = 0 := by
        rw [show k + 1 = B.darts.length by omega, Nat.mod_self]
      have hpos : 0 < B.darts.length := by omega
      rw [hmod, List.getElem?_eq_getElem hpos]
      have hc := B.closes
      rw [List.getLast_eq_getElem, List.head_eq_getElem] at hc
      have hk' : k = B.darts.length - 1 := by omega
      subst hk'
      exact congrArg some hc.symm
  induction r with
  | zero =>
    rw [Nat.add_zero, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj, pow_zero,
      Equiv.Perm.one_apply]
  | succ r ih =>
    have hpos : 0 < B.darts.length := by omega
    have hk : (j + r) % B.darts.length < B.darts.length := Nat.mod_lt _ hpos
    rw [List.getElem?_eq_getElem hk, Option.some_inj] at ih
    have e : (j + (r + 1)) % B.darts.length =
        ((j + r) % B.darts.length + 1) % B.darts.length := by
      rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [e, step hk, ih, pow_succ', Equiv.Perm.mul_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.getElem?_add_mod_length

/-- `facePerm ^ length` fixes every dart of a face boundary.  Osin math/0411039v3, Lemma 9.4,
inside Hull's proof of `thm:hull`: a face walk that goes once around a cell returns to its
first dart. -/
theorem FaceBoundary.pow_length_apply {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {d : M.Dart} (hd : d ∈ B.darts) : (M.facePerm ^ B.darts.length) d = d := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  have h := B.getElem?_add_mod_length hj B.darts.length
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj, Option.some_inj] at h
  exact h.symm

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.pow_length_apply

/-- The first `m ≤ length` darts of a face boundary rotated to position `j` are the face walk
of length `m` from the dart at position `j`.  Osin math/0411039v3, Lemma 9.4, inside Hull's
proof of `thm:hull`: a subpath of a cell boundary is read by `facePerm`. -/
theorem FaceBoundary.rotate_take_eq_map_pow {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {j m : ℕ} (hj : j < B.darts.length) (hm : m ≤ B.darts.length) :
    (B.darts.rotate j).take m =
      (List.range m).map fun r => (M.facePerm ^ r) (B.darts[j]'hj) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_rotate, List.length_map, List.length_range]
    omega
  · intro r _ _
    simp only [List.getElem_take, List.getElem_rotate, List.getElem_map, List.getElem_range]
    have hpos : 0 < B.darts.length := by omega
    have h := B.getElem?_add_mod_length hj r
    rw [Nat.add_comm j r, List.getElem?_eq_getElem (Nat.mod_lt (r + j) hpos),
      Option.some_inj] at h
    exact h

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.rotate_take_eq_map_pow

/-- A nonempty list in which each entry is `p` of the previous one is the `p`-walk from its
head.  Osin math/0411039v3, Lemma 9.4, inside Hull's proof of `thm:hull`: a class of polygon
sides read along a cell is a face walk. -/
theorem List.eq_map_pow_of_isChain {α : Type*} (p : Equiv.Perm α) {l : List α} (hne : l ≠ [])
    (hl : l.IsChain fun d e => p d = e) :
    l = (List.range l.length).map fun r => (p ^ r) (l.head hne) := by
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have key : ∀ (r : ℕ) (hr : r < l.length), l[r] = (p ^ r) (l[0]'hpos) := by
    intro r
    induction r with
    | zero =>
      intro _
      rw [pow_zero, Equiv.Perm.one_apply]
    | succ r ih =>
      intro hr
      rw [pow_succ', Equiv.Perm.mul_apply, ← ih (by omega)]
      exact ((List.isChain_iff_getElem.mp hl) r hr).symm
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro r h₁ _
    simp only [List.getElem_map, List.getElem_range, List.head_eq_getElem]
    exact key r h₁

#audit_axioms GroupApproximation.GGT.VanKampen.List.eq_map_pow_of_isChain

namespace Embedded

/-- A face walk of length `m ≤ length` from a dart on the boundary of a relator cell is a cyclic
arc of that cell.  Osin math/0411039v3, Lemma 9.4, inside Hull's proof of `thm:hull`: the darts
of a class on a cell form an arc of the cell boundary. -/
theorem CyclicArc.exists_darts_eq_map_pow
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (i : Fin Delta.rCellCount)
    {d : Delta.toCombMap.Dart} (hd : d ∈ cellDarts Delta i) {m : ℕ}
    (hm : m ≤ (cellDarts Delta i).length) :
    ∃ arc : CyclicArc (cellDarts Delta i),
      arc.darts = (List.range m).map fun r => (Delta.toCombMap.facePerm ^ r) d := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  refine ⟨⟨⟨j, by omega⟩, m, hm⟩, ?_⟩
  rw [CyclicArc.darts, CyclicArc.rotated_eq_rotate]
  exact FaceBoundary.rotate_take_eq_map_pow (Delta.faceBoundary (cell Delta i).face) hj hm

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.exists_darts_eq_map_pow

end Embedded

/-- A face walk from a boundary dart that is longer than the boundary visits that dart at least
twice, at steps `0` and `length`.  Osin math/0411039v3, Lemma 9.4, inside Hull's proof of
`thm:hull`: a class on a cell has no more darts than the cell boundary. -/
theorem FaceBoundary.two_le_count_map_pow {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    [DecidableEq M.Dart] {d : M.Dart} (hd : d ∈ B.darts) {m : ℕ} (hm : B.darts.length < m) :
    2 ≤ ((List.range m).map fun r => (M.facePerm ^ r) d).count d := by
  have hpos : 0 < B.darts.length := List.length_pos_of_mem hd
  have h0 : 1 ≤ ((List.range B.darts.length).map fun r => (M.facePerm ^ r) d).count d :=
    List.one_le_count_iff.mpr (List.mem_map.mpr
      ⟨0, List.mem_range.mpr hpos, by simp only [pow_zero, Equiv.Perm.one_apply]⟩)
  obtain ⟨k, rfl⟩ : ∃ k, m = B.darts.length + 1 + k := ⟨m - (B.darts.length + 1), by omega⟩
  rw [List.range_add, List.range_succ]
  simp only [List.map_append, List.map_cons, List.map_nil, List.count_append,
    B.pow_length_apply hd, List.count_singleton_self]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.two_le_count_map_pow

end GroupApproximation.GGT.VanKampen
