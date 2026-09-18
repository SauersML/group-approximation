import GroupApproximation.Manuscript.NonMF.Full.GL06a.ObjectWords
import GroupApproximation.Manuscript.NonMF.Full.GL06a.ObjectGeometry
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06a: the object changes of a rich polygon

This is infrastructure for `thm:hull` in non_mf_groups_exist.tex.  It enters through the contact
count in the proof of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), which feeds the relative
Greendlinger lemma (Osin, Lemma 4.4).  It certifies no printed sentence on its own.

`objectChangesStatement : OsinLemma94ObjectChangesStatement` says that a polygon with `d ≥ 2`
neighbours has at most `2 d` object changes.

Polygon `k` reads the word `objWord P k` of the objects across its sides.  The letter is `none`
for a cutting or short side.
* An object change `s < N - 1` is a change position of the word (`objectChanges_subset`); the
  wrap-around position `N - 1` costs one more.
* There are at most `|R| - 1` change positions, where `R` is the reduced word
  (`card_changePositions_le`).
* `R` has no equal neighbours, and planarity (`no_interleave`) gives it no subsequence `a b a b`.
  So `|R| + 1 ≤ 2 #R ≤ 2 d` (`length_add_one_le_two_mul_card`).
-/

namespace GroupApproximation.Full.GL06a

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- The word of objects read along polygon `k`: the object across each side, `none` for a
cutting or short side. -/
def objWord (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    List (Option (Option (Fin S.diagram.rCellCount))) :=
  (List.range (P.sideCount k)).map fun s => OsinLemma94RealizedPolygons.sideObject (P.kind k s)

theorem objWord_getElem? (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {s : ℕ}
    (hs : s < P.sideCount k) :
    (objWord P k)[s]? = some (OsinLemma94RealizedPolygons.sideObject (P.kind k s)) := by
  rw [objWord, List.getElem?_map, List.getElem?_range hs, Option.map_some]

/-- **An object change reads two different objects** at side `s` and the next side. -/
theorem exists_objects_of_mem_objectChanges (P : OsinLemma94RealizedPolygons S)
    {k : Fin P.count} {s : ℕ} (hs : s ∈ P.objectChanges k) :
    s < P.sideCount k ∧ ∃ o o' : Option (Fin S.diagram.rCellCount), o ≠ o' ∧
      OsinLemma94RealizedPolygons.sideObject (P.kind k s) = some o ∧
      OsinLemma94RealizedPolygons.sideObject (P.kind k ((s + 1) % P.sideCount k)) = some o' := by
  obtain ⟨hcont, hnb⟩ := Finset.mem_filter.mp hs
  have hlong : s ∈ P.longTransitions k := (Finset.mem_filter.mp hcont).1
  have hrun : s ∈ P.runEnds k := (Finset.mem_filter.mp hlong).1
  obtain ⟨hrange, hkind, -⟩ := Finset.mem_filter.mp hrun
  refine ⟨Finset.mem_range.mp hrange, ?_⟩
  have hne := P.kind_ne_next_of_mem_longTransitions hlong
  have hnext := P.next_kind_of_mem_contactTransitions hcont
  cases hk : P.kind k s with
  | cell j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' =>
      have hjj : j ≠ j' := fun h => hne (by rw [hk, hn, h])
      exact ⟨some j, some j', fun h => hjj (Option.some_injective _ h), rfl, rfl⟩
    | boundary _ => exact ⟨some j, none, Option.some_ne_none j, rfl, rfl⟩
    | cutting =>
      rcases hnext with ⟨_, h⟩ | ⟨_, h⟩
      · rw [hn] at h
        cases h
      · rw [hn] at h
        cases h
    | short =>
      rcases hnext with ⟨_, h⟩ | ⟨_, h⟩
      · rw [hn] at h
        cases h
      · rw [hn] at h
        cases h
  | boundary j =>
    cases hn : P.kind k ((s + 1) % P.sideCount k) with
    | cell j' => exact ⟨none, some j', (Option.some_ne_none j').symm, rfl, rfl⟩
    | boundary j' => exact (hnb ⟨⟨j, hk⟩, ⟨j', hn⟩⟩).elim
    | cutting =>
      rcases hnext with ⟨_, h⟩ | ⟨_, h⟩
      · rw [hn] at h
        cases h
      · rw [hn] at h
        cases h
    | short =>
      rcases hnext with ⟨_, h⟩ | ⟨_, h⟩
      · rw [hn] at h
        cases h
      · rw [hn] at h
        cases h
  | cutting =>
    rcases hkind with ⟨_, h⟩ | ⟨_, h⟩
    · rw [hk] at h
      cases h
    · rw [hk] at h
      cases h
  | short =>
    rcases hkind with ⟨_, h⟩ | ⟨_, h⟩
    · rw [hk] at h
      cases h
    · rw [hk] at h
      cases h

/-- **The object changes are change positions of the word**, up to the last side. -/
theorem objectChanges_subset (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    P.objectChanges k ⊆ insert (P.sideCount k - 1) (changePositions (objWord P k)) := by
  intro s hs
  obtain ⟨hslt, o, o', hoo', ho, ho'⟩ := exists_objects_of_mem_objectChanges P hs
  rcases Nat.lt_or_ge (s + 1) (P.sideCount k) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at ho'
    refine Finset.mem_insert_of_mem (mem_changePositions hoo' (objWord P k) s ?_ ?_)
    · rw [objWord_getElem? P k hslt, ho]
    · rw [objWord_getElem? P k hlt, ho']
  · have hs' : s = P.sideCount k - 1 := by omega
    rw [hs']
    exact Finset.mem_insert_self _ _

/-- The reduced word of polygon `k` has no equal neighbours. -/
theorem objWord_isChain (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (reducedWord (objWord P k)).IsChain (· ≠ ·) :=
  List.isChain_destutter _ _

/-- **The reduced word of polygon `k` has no subsequence `a b a b`**, by planarity. -/
theorem objWord_noABAB (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    NoABAB (reducedWord (objWord P k)) := by
  rw [reducedWord, objWord, reduceOption_map]
  exact (noABAB_filterMap_range
    (g := fun s => OsinLemma94RealizedPolygons.sideObject (P.kind k s)) (n := P.sideCount k)
    fun _ _ _ _ _ _ h12 h23 h34 h4 hab ha1 hb2 ha3 hb4 =>
      no_interleave P k h12 h23 h34 h4 hab ha1 hb2 ha3 hb4).sublist
    (List.destutter_sublist _ _)

/-- The letters of the reduced word are neighbours of polygon `k`. -/
theorem reducedWord_toFinset_subset (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    (reducedWord (objWord P k)).toFinset ⊆ P.neighbours k := by
  intro o ho
  have hmem : some o ∈ (List.range (P.sideCount k)).map
      fun s => OsinLemma94RealizedPolygons.sideObject (P.kind k s) :=
    some_mem_of_mem_reducedWord (List.mem_toFinset.mp ho)
  obtain ⟨s, hs, hso⟩ := List.mem_map.mp hmem
  exact (P.mem_neighbours k o).mpr ⟨s, List.mem_range.mp hs, hso⟩

/-- **A rich polygon has at most `2 d_k` object changes** (Osin, Lemma 9.4). -/
theorem objectChanges_card_le (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    (hrich : P.Rich k) : (P.objectChanges k).card ≤ 2 * (P.neighbours k).card := by
  have hcp := card_changePositions_le (objWord P k)
  have h1 : (P.objectChanges k).card ≤ (changePositions (objWord P k)).card + 1 :=
    (Finset.card_le_card (objectChanges_subset P k)).trans (Finset.card_insert_le _ _)
  have hrich' : 2 ≤ (P.neighbours k).card := hrich
  by_cases hne : reducedWord (objWord P k) = []
  · have h0 : (reducedWord (objWord P k)).length = 0 := by
      rw [hne, List.length_nil]
    omega
  · have hword := length_add_one_le_two_mul_card (reducedWord (objWord P k)).length
      (reducedWord (objWord P k)) le_rfl hne (objWord_isChain P k) (objWord_noABAB P k)
    have hfin : (reducedWord (objWord P k)).toFinset.card ≤ (P.neighbours k).card :=
      Finset.card_le_card (reducedWord_toFinset_subset P k)
    omega

/-- **The object changes of Lemma 9.4** (`OsinLemma94ObjectChangesStatement`): a polygon with
`d ≥ 2` neighbours has at most `2 d` object changes. -/
theorem objectChangesStatement :
    GroupApproximation.GGT.VanKampen.OsinLemma94ObjectChangesStatement.{u, w, v} :=
  fun _ P k hrich => objectChanges_card_le P k hrich

end GroupApproximation.Full.GL06a

#audit_axioms GroupApproximation.Full.GL06a.objectChangesStatement
