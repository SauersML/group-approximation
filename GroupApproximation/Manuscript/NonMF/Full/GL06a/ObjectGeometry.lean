import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ContactWords
import GroupApproximation.GGT.VanKampen.Estimating.OsinUnboundSameCellCycle
import GroupApproximation.GGT.VanKampen.CombMapNeighbourFacesNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06a: four sides of a polygon never read `a b a b`

This is infrastructure for `thm:hull` in non_mf_groups_exist.tex.  It enters through the object
change count in the proof of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), which feeds the relative
Greendlinger lemma (Osin, Lemma 4.4).  It certifies no printed sentence on its own.

Rotate the walk of `face k` by `base k`: the result is the concatenation of the sides.  Side `i`
starts at position `sidePos P k i` of the rotated walk, and these positions strictly increase
(`sidePos_lt_sidePos`).  So the first dart of side `i` is `facePerm ^ (sidePos k i - sidePos k i₁)`
applied to the first dart of side `i₁ ≤ i` (`sideHead_eq_pow`).  The face across a dart of a side
along object `o` is `objectFace S o` (`faceOf_alpha_of_mem_sideDarts`).

If sides `i₁ < i₂ < i₃ < i₄` read objects `a, b, a, b` with `a ≠ b`, the faces across the face walk
of `face k` read `A, B, A, B` at increasing positions.  Here `A ≠ B`, and neither equals `face k`.
Planarity rules this out (`NeighbourFaces.false_of_interleave`); see `no_interleave`.
-/

namespace GroupApproximation.Full.GL06a

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- **The face across a side along object `o`** is the face of `o` (Osin, Lemma 9.4). -/
theorem faceOf_alpha_of_mem_sideDarts (P : OsinLemma94RealizedPolygons S) {k : Fin P.count}
    {s : ℕ} (hs : s < P.sideCount k) {o : Option (Fin S.diagram.rCellCount)}
    (hobj : OsinLemma94RealizedPolygons.sideObject (P.kind k s) = some o)
    {d : S.diagram.toCombMap.Dart} (hmem : d ∈ P.sideDarts k s) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d) =
      OsinLemma94RealizedPolygons.objectFace S o := by
  cases hkind : P.kind k s with
  | cell j =>
    rw [hkind] at hobj
    have ho : o = some j := (Option.some_injective _ hobj).symm
    subst ho
    obtain ⟨arc, harc⟩ := P.cell_arc k s j hs hkind
    rw [harc] at hmem
    simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at hmem
    obtain ⟨e, he, hre⟩ := hmem
    rw [← hre, S.diagram.toCombMap.alpha_involutive e]
    exact ((S.diagram.faceBoundary (Embedded.cell S.diagram j).face).mem_iff e).mp
      (arc.mem_cycle_of_mem_darts he)
  | boundary j =>
    rw [hkind] at hobj
    have ho : o = none := (Option.some_injective _ hobj).symm
    subst ho
    obtain ⟨_, arc, harc, -, -⟩ := P.boundary_arc k s j hs hkind
    rw [harc] at hmem
    have hout : d ∈ outerDarts S.diagram := arc.mem_cycle_of_mem_darts hmem
    simp only [outerDarts, List.mem_map, List.mem_reverse] at hout
    obtain ⟨e, he, hre⟩ := hout
    rw [← hre, S.diagram.toCombMap.alpha_involutive e]
    exact ((S.diagram.faceBoundary S.diagram.outerFace).mem_iff e).mp he
  | cutting =>
    rw [hkind] at hobj
    exact absurd hobj (by simp [OsinLemma94RealizedPolygons.sideObject])
  | short =>
    rw [hkind] at hobj
    exact absurd hobj (by simp [OsinLemma94RealizedPolygons.sideObject])

theorem length_flatMap_range_le {β : Type*} (f : ℕ → List β) {i j : ℕ} (hij : i ≤ j) :
    ((List.range i).flatMap f).length ≤ ((List.range j).flatMap f).length := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst hi
    exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have h' := ih (by omega)
      simp only [List.range_succ, List.flatMap_append, List.length_append]
      omega
    · have hi : i = j + 1 := by omega
      subst hi
      exact le_refl _

/-- Position `|f 0 ++ ⋯ ++ f (i-1)| + t` of `f 0 ++ ⋯ ++ f (n-1)` is position `t` of `f i`. -/
theorem getElem?_flatMap_range {β : Type*} (f : ℕ → List β) {n i t : ℕ} (hi : i < n)
    (ht : t < (f i).length) :
    ((List.range n).flatMap f)[((List.range i).flatMap f).length + t]? = (f i)[t]? := by
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases h : i < n
    · have hle := length_flatMap_range_le f (show i + 1 ≤ n by omega)
      simp only [List.range_succ, List.flatMap_append, List.length_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at hle
      have hlt : ((List.range i).flatMap f).length + t < ((List.range n).flatMap f).length := by
        omega
      rw [List.getElem?_append_left hlt, ih h]
    · have hin : i = n := by omega
      rw [← hin]
      have hle : ((List.range i).flatMap f).length ≤ ((List.range i).flatMap f).length + t :=
        Nat.le_add_right _ _
      rw [List.getElem?_append_right hle, Nat.add_sub_cancel_left,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The position on the rotated walk of polygon `k` where side `i` starts. -/
def sidePos (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) : ℕ :=
  ((List.range i).flatMap (P.sideDarts k)).length

theorem sidePos_lt_sidePos (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i j : ℕ}
    (hij : i < j) (hj : j ≤ P.sideCount k) : sidePos P k i < sidePos P k j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hlen : 0 < (P.sideDarts k m).length :=
    List.length_pos_iff.mpr (P.side_ne_nil k m (by omega))
  have hle := length_flatMap_range_le (P.sideDarts k) (show i ≤ m by omega)
  simp only [sidePos, List.range_succ, List.flatMap_append, List.length_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  omega

theorem sidePos_sideCount (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    sidePos P k (P.sideCount k) = (S.diagram.faceBoundary (P.face k)).darts.length := by
  rw [sidePos, ← P.walk k, List.length_rotate]

/-- The first dart of side `i` sits at position `sidePos k i` of the rotated walk. -/
theorem getElem?_rotate_sidePos (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i : ℕ}
    (hi : i < P.sideCount k) :
    ((S.diagram.faceBoundary (P.face k)).darts.rotate (P.base k))[sidePos P k i]? =
      (P.sideDarts k i).head? := by
  have hlen : 0 < (P.sideDarts k i).length := List.length_pos_iff.mpr (P.side_ne_nil k i hi)
  have h := getElem?_flatMap_range (P.sideDarts k) hi hlen
  rw [P.walk k, List.head?_eq_getElem?]
  exact h

/-- **The first dart of side `i`** is a face step from the first dart of side `i₁ ≤ i`. -/
theorem sideHead_eq_pow (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i1 i : ℕ}
    (hi1 : i1 ≤ i) (hi : i < P.sideCount k)
    (hk0 : (sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length <
      (S.diagram.faceBoundary (P.face k)).darts.length) :
    (P.sideDarts k i).head? =
      some ((S.diagram.toCombMap.facePerm ^ (sidePos P k i - sidePos P k i1))
        ((S.diagram.faceBoundary (P.face k)).darts[(sidePos P k i1 + P.base k) %
          (S.diagram.faceBoundary (P.face k)).darts.length]'hk0)) := by
  have hposlt : sidePos P k i < (S.diagram.faceBoundary (P.face k)).darts.length := by
    rw [← sidePos_sideCount P k]
    exact sidePos_lt_sidePos P k hi (le_refl _)
  have hmono : sidePos P k i1 ≤ sidePos P k i := by
    rcases Nat.lt_or_ge i1 i with h | h
    · exact (sidePos_lt_sidePos P k h hi.le).le
    · have he : i1 = i := by omega
      subst he
      exact le_refl _
  have hidx : (sidePos P k i + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length =
      ((sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length +
        (sidePos P k i - sidePos P k i1)) % (S.diagram.faceBoundary (P.face k)).darts.length := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  have hlt : ((sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length +
      (sidePos P k i - sidePos P k i1)) % (S.diagram.faceBoundary (P.face k)).darts.length <
        (S.diagram.faceBoundary (P.face k)).darts.length :=
    Nat.mod_lt _ (by omega)
  rw [← getElem?_rotate_sidePos P k hi, List.getElem?_rotate hposlt, hidx,
    List.getElem?_eq_getElem hlt,
    GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.getElem_mod_pow
      (S.diagram.faceBoundary (P.face k)) hk0]

/-- The face across the first dart of a side along `o`, as a face step from side `i₁`. -/
theorem faceOf_alpha_pow_of_side (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {i1 i : ℕ} (hi1 : i1 ≤ i) (hi : i < P.sideCount k)
    (hk0 : (sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length <
      (S.diagram.faceBoundary (P.face k)).darts.length)
    {o : Option (Fin S.diagram.rCellCount)}
    (hobj : OsinLemma94RealizedPolygons.sideObject (P.kind k i) = some o) :
    S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      ((S.diagram.toCombMap.facePerm ^ (sidePos P k i - sidePos P k i1))
        ((S.diagram.faceBoundary (P.face k)).darts[(sidePos P k i1 + P.base k) %
          (S.diagram.faceBoundary (P.face k)).darts.length]'hk0))) =
      OsinLemma94RealizedPolygons.objectFace S o :=
  faceOf_alpha_of_mem_sideDarts P hi hobj
    (List.mem_of_mem_head? (Option.mem_def.mpr (sideHead_eq_pow P k hi1 hi hk0)))

/-- **No four sides read `a b a b`**, by planarity of the diagram (Osin, Lemma 9.4). -/
theorem no_interleave (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i1 i2 i3 i4 : ℕ}
    (h12 : i1 < i2) (h23 : i2 < i3) (h34 : i3 < i4) (h4 : i4 < P.sideCount k)
    {a b : Option (Fin S.diagram.rCellCount)} (hab : a ≠ b)
    (ha1 : OsinLemma94RealizedPolygons.sideObject (P.kind k i1) = some a)
    (hb2 : OsinLemma94RealizedPolygons.sideObject (P.kind k i2) = some b)
    (ha3 : OsinLemma94RealizedPolygons.sideObject (P.kind k i3) = some a)
    (hb4 : OsinLemma94RealizedPolygons.sideObject (P.kind k i4) = some b) : False := by
  have hL := sidePos_sideCount P k
  have hp12 := sidePos_lt_sidePos P k h12 (by omega)
  have hp23 := sidePos_lt_sidePos P k h23 (by omega)
  have hp34 := sidePos_lt_sidePos P k h34 (by omega)
  have hp4 := sidePos_lt_sidePos P k h4 (le_refl _)
  have hk0 : (sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length <
      (S.diagram.faceBoundary (P.face k)).darts.length := Nat.mod_lt _ (by omega)
  have hA1 := faceOf_alpha_pow_of_side P k (le_refl i1) (by omega) hk0 ha1
  rw [Nat.sub_self, pow_zero, Equiv.Perm.one_apply] at hA1
  have hB2 := faceOf_alpha_pow_of_side P k h12.le (by omega) hk0 hb2
  have hA3 := faceOf_alpha_pow_of_side P k (show i1 ≤ i3 by omega) (by omega) hk0 ha3
  have hB4 := faceOf_alpha_pow_of_side P k (show i1 ≤ i4 by omega) h4 hk0 hb4
  have hx0 : S.diagram.toCombMap.faceOf ((S.diagram.faceBoundary (P.face k)).darts[
      (sidePos P k i1 + P.base k) % (S.diagram.faceBoundary (P.face k)).darts.length]'hk0) =
        P.face k :=
    ((S.diagram.faceBoundary (P.face k)).mem_iff _).mp (List.getElem_mem hk0)
  refine GroupApproximation.GGT.VanKampen.NeighbourFaces.false_of_interleave
    S.diagram.toCombMap S.diagram.planar _
    (S.diagram.faceBoundary (P.face k)).darts.length
    (GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.pow_length
      (S.diagram.faceBoundary (P.face k)) hk0)
    (fun x y hx hy h =>
      GroupApproximation.GGT.VanKampen.OsinUnboundSameCellCycle.pow_inj
        (S.diagram.faceBoundary (P.face k)) hk0 hx hy h)
    (r := sidePos P k i2 - sidePos P k i1) (q := sidePos P k i3 - sidePos P k i1)
    (s := sidePos P k i4 - sidePos P k i1) (by omega) (by omega) (by omega) (by omega)
    (hA1.trans hA3.symm) (hB2.trans hB4.symm) ?_ ?_ ?_
  · rw [hA1, hB2]
    exact fun h => hab (OsinLemma94RealizedPolygons.objectFace_injective S h)
  · rw [hA1, hx0]
    exact P.objectFace_ne_face k a
  · rw [hB2, hx0]
    exact P.objectFace_ne_face k b

end GroupApproximation.Full.GL06a

#audit_axioms GroupApproximation.Full.GL06a.no_interleave
