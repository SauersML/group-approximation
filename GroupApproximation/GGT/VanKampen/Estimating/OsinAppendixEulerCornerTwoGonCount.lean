import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerCornerTwoGon
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import GroupApproximation.Meta.AxiomGuard

/-!
# At most `r` two-gons at the outer vertex hold a corner in their gap

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.3.  This module proves
`CornerTwoGonInput` (`Estimating/OsinAppendixEulerCornerTwoGon.lean`), C4 of the plan in
`notes/nm-swarm/reports/hull-euler.md`.

Let `B` be the boundary cycle of the outer face and `L` its length.  The outer face lies in no
region, so the collapsed map rotates it as `Delta` does.  An exterior region `a` with target arc
starting at `s` crosses `O` at the dart `B[L - 1 - s]`.  Let `y` be the dart of a two-gon at `O`.
The rotation of `Φ'_M` is the first return of the collapsed face rotation, so the dart `z` before
`y` lies `m` steps back along `B`, and no exterior region crosses `O` in between.  So the region
`b` of `z`, two steps on from `y` around the face, has its target arc start `m` steps after the
start of `a`, and no other exterior target arc starts in between.

* `eq_of_targetArc_overlap`: two exterior target arcs through one position of `∂Δ` belong to one
  region;
* `exists_gap_offset`: a corner in the gap of `y` lies strictly after the start of `a` and at most
  `m` steps on, and every other exterior target arc starts at least `m` steps on;
* `eq_of_gapHoldsCorner`: two darts at `O` of two-gons whose gaps hold one corner are equal;
* `cornerTwoGonInput`: the count, by double counting over the corners.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

private theorem mod_eq_of_cases {n j L : ℕ} (hj : j < L) (h : n = j ∨ n = j + L) :
    n % L = j := by
  rcases h with rfl | rfl
  · exact Nat.mod_eq_of_lt hj
  · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hj]

private theorem cases_of_mod_eq {n j L : ℕ} (hn : n < L + L) (h : n % L = j) :
    n = j ∨ n = j + L := by
  subst h
  by_cases hlt : n < L
  · left
    rw [Nat.mod_eq_of_lt hlt]
  · right
    have h1 : n ≥ L := by omega
    rw [Nat.mod_eq_sub_mod h1]
    have h2 : n - L < L := by omega
    rw [Nat.mod_eq_of_lt h2]
    omega

private theorem index_eq_of_getElem?_eq {α : Type*} {l : List α} (hl : l.Nodup) {i j : ℕ}
    {a : α} (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', rfl⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hj''⟩ := List.getElem?_eq_some_iff.mp hj
  exact (hl.getElem_inj_iff).mp hj''.symm

private theorem offset_cases_of_mod {L sa sb m : ℕ} (hsa : sa < L) (hsb : sb < L) (hmL : m ≤ L)
    (hmod : (L - 1 - sb + m) % L = L - 1 - sa) : m + sa = sb ∨ m + sa = sb + L := by
  have hn : L - 1 - sb + m < L + L := by omega
  rcases cases_of_mod_eq hn hmod with h | h <;> omega

private theorem le_of_mod_ne {L sa sb sx m u : ℕ} (hsa : sa < L) (hsb : sb < L) (hsx : sx < L)
    (hm : m + sa = sb ∨ m + sa = sb + L)
    (hnot : ∀ k, 0 < k → k < m → (L - 1 - sb + k) % L ≠ L - 1 - sx)
    (hu : 0 < u) (hx : sx = sa + u ∨ sx + L = sa + u) : m ≤ u := by
  by_contra hlt
  have hj : L - 1 - sx < L := by omega
  have hcase : L - 1 - sb + (m - u) = L - 1 - sx ∨ L - 1 - sb + (m - u) = L - 1 - sx + L := by
    omega
  exact hnot (m - u) (by omega) (by omega) (mod_eq_of_cases hj hcase)

/-- One step along a face boundary, cyclically. -/
theorem FaceBoundary.getElem?_succ_mod_length {M : CombMap} {f : M.Face} (B : FaceBoundary M f)
    {j : ℕ} (hj : j < B.darts.length) :
    B.darts[(j + 1) % B.darts.length]? = some (M.facePerm (B.darts[j]'hj)) := by
  by_cases h : j + 1 < B.darts.length
  · rw [Nat.mod_eq_of_lt h, List.getElem?_eq_getElem h]
    exact congrArg some ((List.isChain_iff_getElem.mp B.chain) j h).symm
  · have hmod : (j + 1) % B.darts.length = 0 := by
      rw [show j + 1 = B.darts.length by omega, Nat.mod_self]
    have hpos : 0 < B.darts.length := by omega
    rw [hmod, List.getElem?_eq_getElem hpos]
    have hc := B.closes
    rw [List.getLast_eq_getElem, List.head_eq_getElem] at hc
    have hj' : j = B.darts.length - 1 := by omega
    subst hj'
    exact congrArg some hc.symm

namespace Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The first dart of a nonempty cyclic arc is the dart at its start. -/
theorem CyclicArc.head?_darts {α : Type*} {cycle : List α} (arc : CyclicArc cycle)
    (hlen : 0 < arc.length) (hs : arc.start.1 < cycle.length) :
    arc.darts.head? = cycle[arc.start.1]? := by
  have hd : 0 < (cycle.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  rw [CyclicArc.darts, CyclicArc.rotated, List.head?_eq_getElem?, List.getElem?_take_of_lt hlen,
    List.getElem?_append_left hd, List.getElem?_drop, Nat.add_zero]

/-- A cyclic arc that does not pass the base point holds the darts between its ends. -/
theorem CyclicArc.getElem_mem_darts {α : Type*} {cycle : List α} (arc : CyclicArc cycle) {p : ℕ}
    (hp : arc.start.1 ≤ p) (hq : p < arc.start.1 + arc.length)
    (hlen : arc.start.1 + arc.length ≤ cycle.length) : cycle[p]'(by omega) ∈ arc.darts := by
  have hlen' : arc.length ≤ (cycle.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  have hp' : p < cycle.length := by omega
  have hi : p - arc.start.1 < arc.length := by omega
  have h3 : (arc.rotated.take arc.length)[p - arc.start.1]? = some (cycle[p]'hp') := by
    rw [CyclicArc.rotated, List.take_append_of_le_length hlen', List.getElem?_take_of_lt hi,
      List.getElem?_drop, show arc.start.1 + (p - arc.start.1) = p by omega,
      List.getElem?_eq_getElem hp']
  exact List.mem_of_getElem? h3

/-- **The crossing dart at the outer vertex of an exterior target arc** is the reverse of its
first dart, the dart `B[L - 1 - s]` of the outer face boundary. -/
theorem head?_map_alpha_of_eq_none (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    (htarget : target = none) (hlen : 0 < arc.length)
    (hs : arc.start.1 < (Delta.faceBoundary Delta.outerFace).darts.length) :
    arc.darts.head?.map Delta.toCombMap.alpha =
      (Delta.faceBoundary Delta.outerFace).darts[
        (Delta.faceBoundary Delta.outerFace).darts.length - 1 - arc.start.1]? := by
  subst htarget
  have hlenT : (targetDarts Delta none).length =
      (Delta.faceBoundary Delta.outerFace).darts.length := by
    simp only [targetDarts, outerDarts, List.length_map, List.length_reverse]
  have hsT : arc.start.1 < (targetDarts Delta none).length := by omega
  have hi : (Delta.faceBoundary Delta.outerFace).darts.length - 1 - arc.start.1 <
      (Delta.faceBoundary Delta.outerFace).darts.length := by omega
  rw [CyclicArc.head?_darts arc hlen hsT]
  change (((Delta.faceBoundary Delta.outerFace).darts.reverse.map
    Delta.toCombMap.alpha)[arc.start.1]?).map Delta.toCombMap.alpha = _
  rw [List.getElem?_map, List.getElem?_reverse hs, List.getElem?_eq_getElem hi, Option.map_some,
    Option.map_some, Delta.toCombMap.alpha_involutive]

/-- An exterior target arc that does not pass the base point holds the boundary darts between its
ends. -/
theorem getElem_outerDarts_mem_targetBoundaryDarts (Delta : DiscDiagram.{u, w, v} W)
    (target : Option (Fin Delta.rCellCount)) (arc : CyclicArc (targetDarts Delta target))
    (htarget : target = none) {p : ℕ} (hp : arc.start.1 ≤ p) (hq : p < arc.start.1 + arc.length)
    (hL : arc.start.1 + arc.length ≤ (outerDarts Delta).length) :
    (outerDarts Delta)[p]'(by omega) ∈ targetBoundaryDarts Delta target arc := by
  subst htarget
  exact arc.getElem_mem_darts hp hq hL

namespace RegionCandidate

variable {D : RelGenSet G Lambda} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {family E : Finset (RegionCandidate D eps Delta)} {lambda c : ℝ}
  {word : List (RelLetter G Lambda)}

/-- The crossing dart of an exterior region at the outer vertex is `B[L - 1 - s]`. -/
theorem crossO_false_true_of_eq_none (a : RegionCandidate D eps Delta) (ht : a.2.target = none)
    (hlen : 0 < a.2.targetArc.length)
    (hs : a.2.targetArc.start.1 < (Delta.faceBoundary Delta.outerFace).darts.length) :
    crossO a false true = (Delta.faceBoundary Delta.outerFace).darts[
      (Delta.faceBoundary Delta.outerFace).darts.length - 1 - a.2.targetArc.start.1]? := by
  rw [crossO_false_of_eq_none a ht]
  change a.2.targetArc.darts.head?.map Delta.toCombMap.alpha = _
  exact head?_map_alpha_of_eq_none Delta a.2.target a.2.targetArc ht hlen hs

/-- **Two exterior target arcs through one position of `∂Δ` belong to one region.** -/
theorem eq_of_targetArc_overlap (P : ExtPhiData family E) {a b : RegionCandidate D eps Delta}
    (ha : a ∈ E) (hb : b ∈ E) (hta : a.2.target = none) (htb : b.2.target = none) {p : ℕ}
    (hpa : a.2.targetArc.start.1 ≤ p) (hqa : p < a.2.targetArc.start.1 + a.2.targetArc.length)
    (hpb : b.2.targetArc.start.1 ≤ p) (hqb : p < b.2.targetArc.start.1 + b.2.targetArc.length)
    (hLa : a.2.targetArc.start.1 + a.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    (hLb : b.2.targetArc.start.1 + b.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length) : a = b := by
  have houter : (outerDarts Delta).length = (Delta.faceBoundary Delta.outerFace).darts.length := by
    simp only [outerDarts, List.length_map, List.length_reverse]
  have hLa' : a.2.targetArc.start.1 + a.2.targetArc.length ≤ (outerDarts Delta).length := by
    omega
  have hLb' : b.2.targetArc.start.1 + b.2.targetArc.length ≤ (outerDarts Delta).length := by
    omega
  have hp : p < (outerDarts Delta).length := by omega
  have hma := getElem_outerDarts_mem_targetBoundaryDarts Delta a.2.target a.2.targetArc hta
    hpa hqa hLa'
  have hmb := getElem_outerDarts_mem_targetBoundaryDarts Delta b.2.target b.2.targetArc htb
    hpb hqb hLb'
  have hca : (outerDarts Delta)[p]'hp ∈ a.2.boundary.cycle := by
    rw [a.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hma)
  have hcb : (outerDarts Delta)[p]'hp ∈ b.2.boundary.cycle := by
    rw [b.2.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hmb)
  exact eq_of_face_mem_of_face_mem P.pairwise (P.subset ha) (P.subset hb)
    ((a.2.boundary.cycle_mem_iff _).mp hca).1 ((b.2.boundary.cycle_mem_iff _).mp hcb).1

/-- Two exterior target arcs start at one position, or the second starts before the first, or
the second starts after the end of the first. -/
theorem start_cases (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    {a b : RegionCandidate D eps Delta} (ha : a ∈ E) (hb : b ∈ E) (hta : a.2.target = none)
    (htb : b.2.target = none) :
    b.2.targetArc.start.1 = a.2.targetArc.start.1 ∨
      b.2.targetArc.start.1 < a.2.targetArc.start.1 ∨
        a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1 := by
  by_contra hne
  have hla := (P.nondegenerate a ha).2
  have hlb := (P.nondegenerate b hb).2
  have hpa : a.2.targetArc.start.1 ≤ b.2.targetArc.start.1 := by omega
  have hqa : b.2.targetArc.start.1 < a.2.targetArc.start.1 + a.2.targetArc.length := by omega
  have hqb : b.2.targetArc.start.1 < b.2.targetArc.start.1 + b.2.targetArc.length := by omega
  have hab := eq_of_targetArc_overlap P ha hb hta htb hpa hqa le_rfl hqb (hbound a ha hta)
    (hbound b hb htb)
  subst hab
  omega

/-- **The collapsed face rotation at the outer face walks along `B`.** -/
theorem outer_collapsed_facePerm_pow (P : ExtPhiData family E) {i : ℕ}
    {x : (collapsedMap family).Dart}
    (hx : (Delta.faceBoundary Delta.outerFace).darts[i]? = some x.1) (k : ℕ) :
    (Delta.faceBoundary Delta.outerFace).darts[
        (i + k) % (Delta.faceBoundary Delta.outerFace).darts.length]? =
      some (((collapsedMap family).facePerm ^ k) x).1 := by
  induction k with
  | zero =>
      obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hx
      rw [Nat.add_zero, Nat.mod_eq_of_lt hi, hx, pow_zero, Equiv.Perm.one_apply]
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      generalize ((collapsedMap family).facePerm ^ k) x = y at ih ⊢
      obtain ⟨hj, hyj⟩ := List.getElem?_eq_some_iff.mp ih
      have hface : ∀ b ∈ family, Delta.toCombMap.faceOf y.1 ∉ b.1 := by
        rw [← hyj, ((Delta.faceBoundary Delta.outerFace).mem_iff _).mp (List.getElem_mem hj)]
        exact P.endFace_not_mem none
      have hstep : ((collapsedMap family).facePerm y).1 = Delta.toCombMap.facePerm y.1 :=
        congrArg Subtype.val (collapsed_facePerm_of_face_not_mem hface)
      rw [hstep, ← Nat.add_assoc, ← Nat.mod_add_mod (i + k) _ 1,
        FaceBoundary.getElem?_succ_mod_length _ hj, hyj]

/-- A face closing after four steps closes after four steps from each of its darts. -/
theorem facePerm_four_of_faceOf_eq (M : CombMap) {d y : M.Dart}
    (h4 : M.facePerm (M.facePerm (M.facePerm (M.facePerm d))) = d)
    (hy : M.faceOf y = M.faceOf d) :
    M.facePerm (M.facePerm (M.facePerm (M.facePerm y))) = y := by
  obtain ⟨i, hi⟩ := ((M.faceOf_eq_iff d y).mp hy.symm).exists_nat_pow_eq
  have hcomm : ∀ x, M.facePerm ((M.facePerm ^ i) x) = (M.facePerm ^ i) (M.facePerm x) := by
    intro x
    rw [← Equiv.Perm.mul_apply, (Commute.self_pow M.facePerm i).eq, Equiv.Perm.mul_apply]
  rw [← hi, hcomm, hcomm, hcomm, hcomm, h4]

/-- The end `O` of a region is its target side, and the region is exterior. -/
theorem side_eq_false_of_sideCellO_eq_none {a : RegionCandidate D eps Delta} {s : Bool}
    (h : sideCellO a s = none) : s = false ∧ a.2.target = none := by
  cases s with
  | true => exact (Option.some_ne_none _ h).elim
  | false => exact ⟨rfl, h⟩

/-- **The dart of `Φ'_M` before the dart at `O` of a two-gon** is a dart at `O` of the region two
steps on around the face. -/
theorem exists_sigma_eq_of_twoGon (P : ExtPhiData family E) (y : (phiMapO family E).Dart)
    (hy : phiCellSideO y = true) (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y) :
    ∃ z : (phiMapO family E).Dart, (phiMapO family E).sigma z = y ∧ phiCellSideO z = true ∧
      sideCellO (phiRegionO z) (phiSideO z) = none ∧
        phiRegionO z =
          phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) := by
  have h1 : ¬ (phiSubdividedMultigraphO P).IsCellDart ((phiMapO family E).facePerm y) :=
    fun h => ((phiSubdividedMultigraphO P).cellDart_facePerm y).mp h hy
  have h2 : (phiSubdividedMultigraphO P).IsCellDart
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)) :=
    ((phiSubdividedMultigraphO P).cellDart_facePerm _).mpr h1
  have h3 : ¬ (phiSubdividedMultigraphO P).IsCellDart ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) :=
    fun h => ((phiSubdividedMultigraphO P).cellDart_facePerm _).mp h h2
  have hz : (phiSubdividedMultigraphO P).IsCellDart ((phiMapO family E).alpha
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm
        ((phiMapO family E).facePerm y)))) :=
    ((phiSubdividedMultigraphO P).cellDart_alpha _).mpr h3
  have hsz : (phiMapO family E).sigma ((phiMapO family E).alpha ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y)))) = y := h4
  have hend := (phiSubdividedMultigraphO P).endCell_sigma _ hz
  rw [hsz] at hend
  refine ⟨_, hsz, hz, hend.symm.trans hO, ?_⟩
  exact ((phiSubdividedMultigraphO P).region_alpha _).trans
    ((phiSubdividedMultigraphO P).facePerm_of_cell _ h2).2.1

/-- **The rotation of `Φ'_M` at `O` is the first return along `B`.**  From the dart `z` at `O`
the rotation reaches the dart `y` at `O` after `m ≤ L` steps along `B`, and no exterior region
crosses `O` strictly in between. -/
theorem exists_outer_return (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    {y z : (phiMapO family E).Dart} (hsz : (phiMapO family E).sigma z = y)
    (hy : phiCellSideO y = true) (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (hz : phiCellSideO z = true) (hzO : sideCellO (phiRegionO z) (phiSideO z) = none) :
    ∃ m : ℕ, 0 < m ∧ m ≤ (Delta.faceBoundary Delta.outerFace).darts.length ∧
      ((Delta.faceBoundary Delta.outerFace).darts.length - 1 -
          (phiRegionO z).2.targetArc.start.1 + m) %
          (Delta.faceBoundary Delta.outerFace).darts.length =
        (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
          (phiRegionO y).2.targetArc.start.1 ∧
      ∀ k, 0 < k → k < m → ∀ x ∈ E, x.2.target = none →
        ((Delta.faceBoundary Delta.outerFace).darts.length - 1 -
            (phiRegionO z).2.targetArc.start.1 + k) %
            (Delta.faceBoundary Delta.outerFace).darts.length ≠
          (Delta.faceBoundary Delta.outerFace).darts.length - 1 - x.2.targetArc.start.1 := by
  obtain ⟨hsy, hty⟩ := side_eq_false_of_sideCellO_eq_none hO
  obtain ⟨hszs, htz⟩ := side_eq_false_of_sideCellO_eq_none hzO
  have hpos : ∀ x ∈ E, x.2.target = none → crossO x false true =
      (Delta.faceBoundary Delta.outerFace).darts[
        (Delta.faceBoundary Delta.outerFace).darts.length - 1 - x.2.targetArc.start.1]? := by
    intro x hx hxt
    have hxa := hbound x hx hxt
    have hxl := (P.nondegenerate x hx).2
    exact crossO_false_true_of_eq_none x hxt hxl (by omega)
  have hyB := phiO_cross y
  rw [hsy, hy, hpos _ (phiRegionO_mem y) hty] at hyB
  have hzB := phiO_cross z
  rw [hszs, hz, hpos _ (phiRegionO_mem z) htz] at hzB
  obtain ⟨m, hm0, hmret, hmnot⟩ := (phiMapO_isRestriction family E).sigma_firstReturn z
  rw [hsz] at hmret
  change ((collapsedMap family).facePerm ^ m) z.1 = y.1 at hmret
  have hpow := outer_collapsed_facePerm_pow P hzB
  have hnot : ∀ k, 0 < k → k < m → ∀ x ∈ E, x.2.target = none →
      ((Delta.faceBoundary Delta.outerFace).darts.length - 1 -
          (phiRegionO z).2.targetArc.start.1 + k) %
          (Delta.faceBoundary Delta.outerFace).darts.length ≠
        (Delta.faceBoundary Delta.outerFace).darts.length - 1 - x.2.targetArc.start.1 := by
    intro k hk0 hkm x hx hxt hmod
    refine hmnot k hk0 hkm
      ⟨⟨((collapsedMap family).facePerm ^ k) z.1, x, hx, false, true, ?_⟩, rfl⟩
    rw [hpos x hx hxt, ← hmod]
    exact hpow k
  have hza := hbound _ (phiRegionO_mem z) htz
  have hzl := (P.nondegenerate _ (phiRegionO_mem z)).2
  have hmL : m ≤ (Delta.faceBoundary Delta.outerFace).darts.length := by
    by_contra hlt
    have hlt' : (Delta.faceBoundary Delta.outerFace).darts.length - 1 -
        (phiRegionO z).2.targetArc.start.1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
      omega
    exact hnot (Delta.faceBoundary Delta.outerFace).darts.length (by omega) (by omega)
      (phiRegionO z) (phiRegionO_mem z) htz (by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt'])
  have hmod := hpow m
  rw [hmret] at hmod
  exact ⟨m, hm0, hmL,
    index_eq_of_getElem?_eq (Delta.faceBoundary Delta.outerFace).nodup hmod hyB, hnot⟩

/-- A corner in the gap after `a` lies strictly after the start of `a` and at most `m` steps on,
where `b` starts `m` steps after `a`. -/
theorem exists_offset_of_gapHoldsCorner (cuts : SectionCuts D lambda c word)
    {a b : RegionCandidate D eps Delta} {k : Fin cuts.count} {L m : ℕ}
    (hk : GapHoldsCorner cuts a b k) (hm0 : 0 < m) (hla : 0 < a.2.targetArc.length)
    (hsa : a.2.targetArc.start.1 + a.2.targetArc.length ≤ L) (hc : cuts.cut k.castSucc ≤ L)
    (hm : m + a.2.targetArc.start.1 = b.2.targetArc.start.1 ∨
      m + a.2.targetArc.start.1 = b.2.targetArc.start.1 + L)
    (hb : b.2.targetArc.start.1 = a.2.targetArc.start.1 ∨
      b.2.targetArc.start.1 < a.2.targetArc.start.1 ∨
        a.2.targetArc.start.1 + a.2.targetArc.length ≤ b.2.targetArc.start.1) :
    ∃ t : ℕ, 0 < t ∧ t ≤ m ∧ (cuts.cut k.castSucc = a.2.targetArc.start.1 + t ∨
      cuts.cut k.castSucc + L = a.2.targetArc.start.1 + t) := by
  unfold GapHoldsCorner at hk
  split_ifs at hk with h
  · exact ⟨cuts.cut k.castSucc - a.2.targetArc.start.1, by omega, by omega, Or.inl (by omega)⟩
  · rcases hk with hk | hk
    · exact ⟨cuts.cut k.castSucc - a.2.targetArc.start.1, by omega, by omega, Or.inl (by omega)⟩
    · exact ⟨cuts.cut k.castSucc + L - a.2.targetArc.start.1, by omega, by omega,
        Or.inr (by omega)⟩

/-- **A corner in the gap of a two-gon at `O`** lies strictly after the start of the region `a` of
the dart at `O` and at most `m` steps on, and every other exterior target arc starts at least `m`
steps after `a`. -/
theorem exists_gap_offset (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    (cuts : SectionCuts D lambda c word)
    (hcut : ∀ k : Fin cuts.count,
      cuts.cut k.castSucc ≤ (Delta.faceBoundary Delta.outerFace).darts.length)
    {k : Fin cuts.count} {y : (phiMapO family E).Dart} (hy : phiCellSideO y = true)
    (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    (hk : GapHoldsCorner cuts (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) k) :
    ∃ m t : ℕ, 0 < t ∧ t ≤ m ∧
      (cuts.cut k.castSucc = (phiRegionO y).2.targetArc.start.1 + t ∨
        cuts.cut k.castSucc + (Delta.faceBoundary Delta.outerFace).darts.length =
          (phiRegionO y).2.targetArc.start.1 + t) ∧
      ∀ x ∈ E, x.2.target = none → ∀ u : ℕ, 0 < u →
        (x.2.targetArc.start.1 = (phiRegionO y).2.targetArc.start.1 + u ∨
          x.2.targetArc.start.1 + (Delta.faceBoundary Delta.outerFace).darts.length =
            (phiRegionO y).2.targetArc.start.1 + u) → m ≤ u := by
  obtain ⟨z, hsz, hz, hzO, hzr⟩ := exists_sigma_eq_of_twoGon P y hy hO h4
  obtain ⟨m, hm0, hmL, hmod, hnot⟩ := exists_outer_return P hbound hsz hy hO hz hzO
  obtain ⟨-, hty⟩ := side_eq_false_of_sideCellO_eq_none hO
  obtain ⟨-, htz⟩ := side_eq_false_of_sideCellO_eq_none hzO
  have hya := hbound _ (phiRegionO_mem y) hty
  have hza := hbound _ (phiRegionO_mem z) htz
  have hyl := (P.nondegenerate _ (phiRegionO_mem y)).2
  have hzl := (P.nondegenerate _ (phiRegionO_mem z)).2
  have hys : (phiRegionO y).2.targetArc.start.1 <
      (Delta.faceBoundary Delta.outerFace).darts.length := by omega
  have hzs : (phiRegionO z).2.targetArc.start.1 <
      (Delta.faceBoundary Delta.outerFace).darts.length := by omega
  have hm := offset_cases_of_mod hys hzs hmL hmod
  have hb := start_cases P hbound (phiRegionO_mem y) (phiRegionO_mem z) hty htz
  rw [← hzr] at hk
  obtain ⟨t, ht0, htm, htc⟩ :=
    exists_offset_of_gapHoldsCorner cuts hk hm0 hyl hya (hcut k) hm hb
  refine ⟨m, t, ht0, htm, htc, fun x hx hxt u hu hxu => ?_⟩
  have hxa := hbound x hx hxt
  have hxl := (P.nondegenerate x hx).2
  have hxs : x.2.targetArc.start.1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
    omega
  exact le_of_mod_ne hys hzs hxs hm (fun j hj0 hjm => hnot j hj0 hjm x hx hxt) hu hxu

/-- **Two darts at `O` of two-gons whose gaps hold one corner are equal.** -/
theorem eq_of_gapHoldsCorner (P : ExtPhiData family E)
    (hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (Delta.faceBoundary Delta.outerFace).darts.length)
    (cuts : SectionCuts D lambda c word)
    (hcut : ∀ k : Fin cuts.count,
      cuts.cut k.castSucc ≤ (Delta.faceBoundary Delta.outerFace).darts.length)
    {k : Fin cuts.count} {y y' : (phiMapO family E).Dart}
    (hy : phiCellSideO y = true) (hO : sideCellO (phiRegionO y) (phiSideO y) = none)
    (h4 : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) = y)
    (hk : GapHoldsCorner cuts (phiRegionO y)
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y))) k)
    (hy' : phiCellSideO y' = true) (hO' : sideCellO (phiRegionO y') (phiSideO y') = none)
    (h4' : (phiMapO family E).facePerm ((phiMapO family E).facePerm
      ((phiMapO family E).facePerm ((phiMapO family E).facePerm y'))) = y')
    (hk' : GapHoldsCorner cuts (phiRegionO y')
      (phiRegionO ((phiMapO family E).facePerm ((phiMapO family E).facePerm y'))) k) :
    y = y' := by
  obtain ⟨hsy, hty⟩ := side_eq_false_of_sideCellO_eq_none hO
  obtain ⟨hsy', hty'⟩ := side_eq_false_of_sideCellO_eq_none hO'
  obtain ⟨m, t, ht0, htm, htc, hF⟩ := exists_gap_offset P hbound cuts hcut hy hO h4 hk
  obtain ⟨m', t', ht0', htm', htc', hF'⟩ :=
    exists_gap_offset P hbound cuts hcut hy' hO' h4' hk'
  have hya := hbound _ (phiRegionO_mem y) hty
  have hya' := hbound _ (phiRegionO_mem y') hty'
  have hyl := (P.nondegenerate _ (phiRegionO_mem y)).2
  have hyl' := (P.nondegenerate _ (phiRegionO_mem y')).2
  have hreg : phiRegionO y = phiRegionO y' := by
    by_contra hne
    have hs : (phiRegionO y).2.targetArc.start.1 ≠ (phiRegionO y').2.targetArc.start.1 := by
      intro hs
      have hqa : (phiRegionO y).2.targetArc.start.1 <
          (phiRegionO y).2.targetArc.start.1 + (phiRegionO y).2.targetArc.length := by omega
      have hqb : (phiRegionO y).2.targetArc.start.1 <
          (phiRegionO y').2.targetArc.start.1 + (phiRegionO y').2.targetArc.length := by omega
      exact hne (eq_of_targetArc_overlap P (phiRegionO_mem y) (phiRegionO_mem y') hty hty'
        le_rfl hqa hs.ge hqb hya hya')
    rcases Nat.lt_or_gt_of_ne hs with hlt | hlt
    · have h1 := hF _ (phiRegionO_mem y') hty'
        ((phiRegionO y').2.targetArc.start.1 - (phiRegionO y).2.targetArc.start.1) (by omega)
        (Or.inl (by omega))
      have h2 := hF' _ (phiRegionO_mem y) hty
        ((phiRegionO y).2.targetArc.start.1 + (Delta.faceBoundary Delta.outerFace).darts.length -
          (phiRegionO y').2.targetArc.start.1) (by omega) (Or.inr (by omega))
      omega
    · have h1 := hF' _ (phiRegionO_mem y) hty
        ((phiRegionO y).2.targetArc.start.1 - (phiRegionO y').2.targetArc.start.1) (by omega)
        (Or.inl (by omega))
      have h2 := hF _ (phiRegionO_mem y') hty'
        ((phiRegionO y').2.targetArc.start.1 + (Delta.faceBoundary Delta.outerFace).darts.length -
          (phiRegionO y).2.targetArc.start.1) (by omega) (Or.inr (by omega))
      omega
  exact dartO_ext hreg (hsy.trans hsy'.symm) (hy.trans hy'.symm)

end RegionCandidate

end Embedded

open scoped Classical in
/-- **C4 of Lemma 9.3**: at most `r` two-gons of `Φ'_M` have a corner in their gap at `O`.  A
corner determines the dart at `O` of a two-gon whose gap holds it (`eq_of_gapHoldsCorner`), and so
the two-gon; count by double counting over the `r` corners. -/
theorem cornerTwoGonInput {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda)
    (lambda c : ℝ) (eps : ℕ) (W : Set (List (RelLetter G Lambda))) :
    CornerTwoGonInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts S E P
  have hL : (S.diagram.faceBoundary S.diagram.outerFace).darts.length =
      Delta.boundaryWord.length := by
    rw [← S.equiv.boundaryWord_eq, ← dartWord_outerDarts S.diagram, dartWord, List.length_map,
      outerDarts, List.length_map, List.length_reverse]
  have hbound : ∀ x ∈ E, x.2.target = none → x.2.targetArc.start.1 + x.2.targetArc.length ≤
      (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    intro x hx hxt
    obtain ⟨j, -, -, hj⟩ := (S.respects x (P.subset hx)).2 hxt
    rw [hL]
    exact hj.trans (cuts.cut_le_length j.succ)
  have hcut : ∀ k : Fin cuts.count,
      cuts.cut k.castSucc ≤ (S.diagram.faceBoundary S.diagram.outerFace).darts.length := by
    intro k
    rw [hL]
    exact cuts.cut_le_length _
  refine le_trans (Finset.card_le_card_of_forall_subsingleton
    (fun (f : (RegionCandidate.phiMapO S.family E).Face) (k : Fin cuts.count) =>
      ∃ y : (RegionCandidate.phiMapO S.family E).Dart,
        (RegionCandidate.phiMapO S.family E).faceOf y = f ∧
          RegionCandidate.phiCellSideO y = true ∧
          RegionCandidate.sideCellO (RegionCandidate.phiRegionO y)
            (RegionCandidate.phiSideO y) = none ∧
          RegionCandidate.GapHoldsCorner cuts (RegionCandidate.phiRegionO y)
            (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family E).facePerm
              ((RegionCandidate.phiMapO S.family E).facePerm y))) k)
    (t := Finset.univ) ?_ ?_) (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin]))
  · intro f hf
    obtain ⟨-, y, hyf, hy, hO, k, hk⟩ := (Finset.mem_filter.mp hf).2
    exact ⟨k, Finset.mem_univ k, y, hyf, hy, hO, hk⟩
  · intro k _ f hf f' hf'
    obtain ⟨hfs, y, hyf, hy, hO, hk⟩ := hf
    obtain ⟨hfs', y', hyf', hy', hO', hk'⟩ := hf'
    obtain ⟨d, -, hdf, hd4, -⟩ := (Finset.mem_filter.mp hfs).2.1
    obtain ⟨d', -, hdf', hd4', -⟩ := (Finset.mem_filter.mp hfs').2.1
    have h4 := RegionCandidate.facePerm_four_of_faceOf_eq (RegionCandidate.phiMapO S.family E)
      hd4 (hyf.trans hdf.symm)
    have h4' := RegionCandidate.facePerm_four_of_faceOf_eq (RegionCandidate.phiMapO S.family E)
      hd4' (hyf'.trans hdf'.symm)
    rw [← hyf, ← hyf', RegionCandidate.eq_of_gapHoldsCorner P hbound cuts hcut hy hO h4 hk
      hy' hO' h4' hk']

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FaceBoundary.getElem?_succ_mod_length
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.head?_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.getElem_mem_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.head?_map_alpha_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.getElem_outerDarts_mem_targetBoundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.crossO_false_true_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eq_of_targetArc_overlap
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.start_cases
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.outer_collapsed_facePerm_pow
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.facePerm_four_of_faceOf_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.side_eq_false_of_sideCellO_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_sigma_eq_of_twoGon
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_outer_return
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_offset_of_gapHoldsCorner
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.exists_gap_offset
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.eq_of_gapHoldsCorner
#audit_axioms GroupApproximation.GGT.VanKampen.cornerTwoGonInput
