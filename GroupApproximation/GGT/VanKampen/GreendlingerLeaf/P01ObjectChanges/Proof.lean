import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.Geometry
import GroupApproximation.Meta.AxiomGuard

/-!
# Object changes of a rich polygon: the count

Endpoint `proof : OsinLemma94ObjectChangesStatement`.  Steps 1 and 5 of the proof in
`P01ObjectChanges.Words`.

* `objWord P k`: the objects across the sides of polygon `k`, in order.
* `mem_objectChanges`: an object change `s` reads different objects at `s` and `(s + 1) % N`.
* `objectChanges_subset`: the object changes lie in the change positions of `objWord`, plus
  `N - 1`.
* `toFinset_compress_subset`: the letters of `compress (objWord P k)` are neighbours.
* `noABAB_compress`: `compress (objWord P k)` has no `a b a b` (`no_interleave`).
* `card_objectChanges_le`: `#objectChanges ≤ #changes + 1 ≤ |compress| ≤ 2 d_k`, by
  `ListNoABAB.length_add_one_le_two_mul_card`, and `≤ 1 ≤ 2 d_k` when `compress` is empty.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The objects across the sides of polygon `k`, in order (`none` for cutting and short sides). -/
def objWord (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    List (Option (Option (Fin S.diagram.rCellCount))) :=
  (List.range (P.sideCount k)).map fun s => OsinLemma94RealizedPolygons.sideObject (P.kind k s)

theorem length_objWord (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (objWord P k).length = P.sideCount k := by
  simp only [objWord, List.length_map, List.length_range]

theorem getElem?_objWord (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {s : ℕ}
    (hs : s < P.sideCount k) :
    (objWord P k)[s]? = some (OsinLemma94RealizedPolygons.sideObject (P.kind k s)) := by
  simp only [objWord, List.getElem?_map, List.getElem?_range hs, Option.map_some]

theorem lt_and_eq_of_getElem? (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {s : ℕ}
    {x : Option (Option (Fin S.diagram.rCellCount))} (h : (objWord P k)[s]? = some x) :
    s < P.sideCount k ∧ OsinLemma94RealizedPolygons.sideObject (P.kind k s) = x := by
  have hs : s < P.sideCount k := by
    obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.mp h
    rw [length_objWord] at hlen
    exact hlen
  refine ⟨hs, ?_⟩
  rw [getElem?_objWord P k hs] at h
  exact Option.some.inj h

/-- **An object change reads two different objects**, at `s` and at the next side. -/
theorem mem_objectChanges (P : OsinLemma94RealizedPolygons S) {k : Fin P.count} {s : ℕ}
    (hs : s ∈ P.objectChanges k) :
    s < P.sideCount k ∧ ∃ a b : Option (Fin S.diagram.rCellCount),
      OsinLemma94RealizedPolygons.sideObject (P.kind k s) = some a ∧
      OsinLemma94RealizedPolygons.sideObject (P.kind k ((s + 1) % P.sideCount k)) = some b ∧
        a ≠ b := by
  obtain ⟨hcont, hnb⟩ := Finset.mem_filter.mp hs
  have hlong : s ∈ P.longTransitions k := (Finset.mem_filter.mp hcont).1
  have hrun : s ∈ P.runEnds k := (Finset.mem_filter.mp hlong).1
  obtain ⟨hrange, hkind, -⟩ := Finset.mem_filter.mp hrun
  have hne := P.kind_ne_next_of_mem_longTransitions hlong
  have hnext := P.next_kind_of_mem_contactTransitions hcont
  refine ⟨Finset.mem_range.mp hrange, ?_⟩
  cases hk : P.kind k s with
  | cell j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' =>
      refine ⟨some j, some j', by first | rfl | (rw [hk]; rfl),
        by first | rfl | (rw [hn]; rfl), fun h => hne ?_⟩
      rw [hk, hn, Option.some_injective _ h]
    | boundary j' =>
      exact ⟨some j, none, by first | rfl | (rw [hk]; rfl), by first | rfl | (rw [hn]; rfl),
        by simp⟩
    | cutting => rw [hn] at hnext; simp at hnext
    | short => rw [hn] at hnext; simp at hnext
  | boundary j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' =>
      exact ⟨none, some j', by first | rfl | (rw [hk]; rfl), by first | rfl | (rw [hn]; rfl),
        by simp⟩
    | boundary j' => exact absurd ⟨⟨j, hk⟩, ⟨j', hn⟩⟩ hnb
    | cutting => rw [hn] at hnext; simp at hnext
    | short => rw [hn] at hnext; simp at hnext
  | cutting => rw [hk] at hkind; simp at hkind
  | short => rw [hk] at hkind; simp at hkind

/-- **The object changes are change positions of the object word, or the last side.** -/
theorem objectChanges_subset (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    P.objectChanges k ⊆ insert (P.sideCount k - 1) (chgSet (objWord P k)) := by
  intro s hs
  obtain ⟨hslt, a, b, ha, hb, hab⟩ := mem_objectChanges P hs
  by_cases hlast : s = P.sideCount k - 1
  · rw [hlast]
    exact Finset.mem_insert_self _ _
  · have hs1 : s + 1 < P.sideCount k := by omega
    rw [Nat.mod_eq_of_lt hs1] at hb
    refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨?_, a, b, ?_, ?_, hab⟩)
    · rw [length_objWord]
      exact Finset.mem_range.mpr hslt
    · rw [getElem?_objWord P k hslt, ha]
    · rw [getElem?_objWord P k hs1, hb]

/-- The letters of the compressed object word are neighbours of the polygon. -/
theorem toFinset_compress_subset (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (compress (objWord P k)).toFinset ⊆ P.neighbours k := by
  intro o ho
  have hmem := some_mem_of_mem_compress (List.mem_toFinset.mp ho)
  obtain ⟨s, hs, hso⟩ := List.mem_map.mp hmem
  exact (P.mem_neighbours k o).mpr ⟨s, List.mem_range.mp hs, hso⟩

/-- **The compressed object word has no `a b a b`**, by planarity. -/
theorem noABAB_compress (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    ListNoABAB.NoABAB (compress (objWord P k)) := by
  refine ListNoABAB.NoABAB.sublist (noABAB_somes ?_) (compress_sublist_somes _)
  intro i1 i2 i3 i4 a b h12 h23 h34 hab h1 h2 h3 h4
  obtain ⟨-, ha1⟩ := lt_and_eq_of_getElem? P k h1
  obtain ⟨-, hb2⟩ := lt_and_eq_of_getElem? P k h2
  obtain ⟨-, ha3⟩ := lt_and_eq_of_getElem? P k h3
  obtain ⟨h4lt, hb4⟩ := lt_and_eq_of_getElem? P k h4
  exact no_interleave P k h12 h23 h34 h4lt hab ha1 hb2 ha3 hb4

/-- **A rich polygon has at most `2 d_k` object changes.** -/
theorem card_objectChanges_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (hrich : P.Rich k) : (P.objectChanges k).card ≤ 2 * (P.neighbours k).card := by
  have h1 : (P.objectChanges k).card ≤ (chgSet (objWord P k)).card + 1 :=
    (Finset.card_le_card (objectChanges_subset P k)).trans (Finset.card_insert_le _ _)
  have h2 := card_chgSet_le (objWord P k)
  have hd : 2 ≤ (P.neighbours k).card := hrich
  by_cases hc : compress (objWord P k) = []
  · rw [hc, List.length_nil] at h2
    omega
  · have h3 := ListNoABAB.length_add_one_le_two_mul_card _ (compress (objWord P k)) rfl hc
      (isChain_compress _) (noABAB_compress P k)
    have h4 := Finset.card_le_card (toFinset_compress_subset P k)
    omega

/-- **Osin's Lemma 9.4, object changes**: a rich polygon has at most `2 d_k` object changes. -/
theorem proof : OsinLemma94ObjectChangesStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ P k hrich
  exact card_objectChanges_le P k hrich

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ObjectChanges.proof
