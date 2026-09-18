import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Windows
import GroupApproximation.Meta.AxiomGuard

/-!
# No junction witness on the 24-dart pocket

Lane gl-p10-51.

`roseJunctionRefute_noWitness`: no data `r, source, kept, t₁, t₂, s₁, s₂` meets the clauses of
`P10RoseExtremalTrim.RoseExtremalJunctionStatement` on `roseJunctionRefute_pK`, once the listing is
a walk.  By the walk class `c = cid r`:
* `c = 0`: the kept cell does not flip (`roseJunctionRefute_flipS`, `roseJunctionRefute_flipK`);
* `c = 1`: the class meets the exterior dart `9`;
* `c = 2`, `c = 4`: the listing is a walk through an isolated dart (`roseJunctionRefute_caseIso`);
* `c = 3`, `c = 5`: the source is `S`, both windows are at their maximum, and the free darts
  `s₁ = [a]`, `s₂ = [b]` leave `b` meeting both junctions (`roseJunctionRefute_tail`).

Proof route: the finite checks of `P10RoseJunctionRefute/Windows`, transported along the
permutation of the listing onto the moved darts.

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

/-- The walk relation of the listing. -/
abbrev roseJunctionRefute_R (d e : roseJunctionRefute_X.toCombMap.Dart) : Prop :=
  roseJunctionRefute_X.toCombMap.vertexOf (roseJunctionRefute_X.toCombMap.alpha d) =
    roseJunctionRefute_X.toCombMap.vertexOf e

/-- The colour of the class of `r`. -/
noncomputable abbrev roseJunctionRefute_col (r : roseJunctionRefute_X.toCombMap.Dart) :
    roseJunctionRefute_X.toCombMap.Dart → Bool :=
  P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap roseJunctionRefute_keep r

/-- The face set after the move of the class of `r`. -/
noncomputable abbrev roseJunctionRefute_flipF (r : roseJunctionRefute_X.toCombMap.Dart) :
    Finset roseJunctionRefute_X.toCombMap.Face :=
  P10Rose.FilterMove.flipFaces roseJunctionRefute_X.toCombMap roseJunctionRefute_pK.faces
    (roseJunctionRefute_col r)

/-- A listing of the moved darts of the class of `r` lists `keptTab (cid r)`. -/
theorem roseJunctionRefute_permF {r : roseJunctionRefute_X.toCombMap.Dart} {c : Fin 6}
    (hc : roseJunctionRefute_cid r = c) {L : List roseJunctionRefute_X.toCombMap.Dart}
    (h : L.Perm (roseJunctionRefute_pK.boundary.cycle.filter
      (P10Rose.FilterMove.movePred roseJunctionRefute_X.toCombMap
        (P10Rose.SubArcMove.regionColour roseJunctionRefute_X.toCombMap
          roseJunctionRefute_keep r)))) :
    L.Perm (roseJunctionRefute_pK.boundary.cycle.filter (roseJunctionRefute_keptTab c)) := by
  rw [roseJunctionRefute_move_eq r c hc] at h
  exact h

/-- **No walk lists a set of darts with an isolated dart.** -/
theorem roseJunctionRefute_caseIso {L F : List roseJunctionRefute_X.toCombMap.Dart}
    (x : roseJunctionRefute_X.toCombMap.Dart) (hL : L.IsChain roseJunctionRefute_R)
    (hp : L.Perm F) (hF : F.Nodup) (hx : x ∈ F) (hlen : 2 ≤ F.length)
    (hiso : ∀ y ∈ F, y ≠ x →
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha x) ≠
        roseJunctionRefute_vClass y ∧
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha y) ≠
        roseJunctionRefute_vClass x) : False := by
  have h := roseJunctionRefute_isolated x L hL (hp.nodup_iff.mpr hF) (hp.mem_iff.mpr hx)
    fun y hy hne =>
      ⟨fun hxy => (hiso y (hp.subset hy) hne).1 ((roseJunctionRefute_vClass_iff _ _).mp hxy),
        fun hyx => (hiso y (hp.subset hy) hne).2 ((roseJunctionRefute_vClass_iff _ _).mp hyx)⟩
  have hl := hp.length_eq
  omega

/-- **The free dart between two maximal windows.**  If `s₁ = [a]`, `s₂ = [b]` and the listing
`s₁ ++ W1 ++ s₂ ++ W2` is a permutation of `F`, then `b` meets the last dart `e` of `W1` and the
first dart `f` of `W2`. -/
theorem roseJunctionRefute_tail {F W1 W2 : List roseJunctionRefute_X.toCombMap.Dart}
    {e f : roseJunctionRefute_X.toCombMap.Dart} (s₁ s₂ : List roseJunctionRefute_X.toCombMap.Dart)
    (hperm : (s₁ ++ W1 ++ s₂ ++ W2).Perm F) (hF : F.Nodup)
    (hs₁ : s₁.length = 1) (hs₂ : s₂.length = 1)
    (he : W1.getLast? = some e) (hh : f ∈ W2.head?)
    (hj₂ : ∀ a ∈ (s₁ ++ W1).getLast?, ∀ b ∈ s₂.head?, roseJunctionRefute_R a b)
    (hj₃ : ∀ a ∈ (s₁ ++ W1 ++ s₂).getLast?, ∀ b ∈ W2.head?, roseJunctionRefute_R a b)
    (hend : ∀ b ∈ F, (W1 ++ [b] ++ W2).Nodup →
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha e) =
        roseJunctionRefute_vClass b →
      roseJunctionRefute_vClass (roseJunctionRefute_X.toCombMap.alpha b) =
        roseJunctionRefute_vClass f → False) : False := by
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hs₁
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hs₂
  have hnd := hperm.nodup_iff.mpr hF
  have hae : e ∈ ([a] ++ W1).getLast? :=
    Option.mem_def.mpr (by rw [List.getLast?_append, he, Option.some_or])
  exact hend b
    (hperm.subset (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)))
    (List.Nodup.sublist (((List.sublist_append_right [a] W1).append_right [b]).append_right W2)
      hnd)
    ((roseJunctionRefute_vClass_iff _ _).mp (hj₂ e hae b (Option.mem_def.mpr List.head?_cons)))
    ((roseJunctionRefute_vClass_iff _ _).mp
      (hj₃ b (Option.mem_def.mpr List.getLast?_concat) f hh))

/-- **The class `3`**: the windows `[6,18,0]` and `[8,20,10,12,22]` leave one free dart. -/
theorem roseJunctionRefute_caseC3 (s₁ s₂ : List roseJunctionRefute_X.toCombMap.Dart)
    (n m p q : ℕ) (hn : n < 8) (hm : m < 7) (hpq : p + q ≤ 5)
    (hperm : (s₁ ++ roseJunctionRefute_win1 n m ++ s₂ ++ roseJunctionRefute_win2 p q).Perm
      roseJunctionRefute_F3)
    (hs₁ : s₁.length ≤ 1) (hs₂ : s₂.length ≤ 1)
    (hj₂ : ∀ a ∈ (s₁ ++ roseJunctionRefute_win1 n m).getLast?, ∀ b ∈ s₂.head?,
      roseJunctionRefute_R a b)
    (hj₃ : ∀ a ∈ (s₁ ++ roseJunctionRefute_win1 n m ++ s₂).getLast?,
      ∀ b ∈ (roseJunctionRefute_win2 p q).head?, roseJunctionRefute_R a b) : False := by
  obtain ⟨h1a, h1b⟩ := roseJunctionRefute_w1c3 n hn m hm fun x hx =>
    hperm.subset (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
  obtain ⟨h2a, h2b⟩ := roseJunctionRefute_w2c3 p (by omega) q (by omega) hpq fun x hx =>
    hperm.subset (List.mem_append_right _ hx)
  have hlen := hperm.length_eq
  simp only [List.length_append] at hlen
  have hF : roseJunctionRefute_F3.length = 10 := rfl
  have e1 : (roseJunctionRefute_win1 n m).length = 3 := by omega
  have e2 : (roseJunctionRefute_win2 p q).length = 5 := by omega
  rw [h1b e1] at hperm hj₂ hj₃
  rw [h2b e2] at hperm hj₃
  exact roseJunctionRefute_tail (e := 0) (f := 8) s₁ s₂ hperm (by decide) (by omega) (by omega)
    rfl (Option.mem_def.mpr rfl) hj₂ hj₃ roseJunctionRefute_endC3

/-- **The class `5`**: the windows `[2,16,4,6,18,0]` and `[8,20]` or `[12,22]` leave one free
dart. -/
theorem roseJunctionRefute_caseC5 (s₁ s₂ : List roseJunctionRefute_X.toCombMap.Dart)
    (n m p q : ℕ) (hn : n < 8) (hm : m < 7) (hpq : p + q ≤ 5)
    (hperm : (s₁ ++ roseJunctionRefute_win1 n m ++ s₂ ++ roseJunctionRefute_win2 p q).Perm
      roseJunctionRefute_F5)
    (hs₁ : s₁.length ≤ 1) (hs₂ : s₂.length ≤ 1)
    (hj₂ : ∀ a ∈ (s₁ ++ roseJunctionRefute_win1 n m).getLast?, ∀ b ∈ s₂.head?,
      roseJunctionRefute_R a b)
    (hj₃ : ∀ a ∈ (s₁ ++ roseJunctionRefute_win1 n m ++ s₂).getLast?,
      ∀ b ∈ (roseJunctionRefute_win2 p q).head?, roseJunctionRefute_R a b) : False := by
  obtain ⟨h1a, h1b⟩ := roseJunctionRefute_w1c5 n hn m hm fun x hx =>
    hperm.subset (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hx)))
  obtain ⟨h2a, h2b⟩ := roseJunctionRefute_w2c5 p (by omega) q (by omega) hpq fun x hx =>
    hperm.subset (List.mem_append_right _ hx)
  have hlen := hperm.length_eq
  simp only [List.length_append] at hlen
  have hF : roseJunctionRefute_F5.length = 10 := rfl
  have e1 : (roseJunctionRefute_win1 n m).length = 6 := by omega
  have e2 : (roseJunctionRefute_win2 p q).length = 2 := by omega
  rw [h1b e1] at hperm hj₂ hj₃
  rcases h2b e2 with hw | hw
  · rw [hw] at hperm hj₃
    exact roseJunctionRefute_tail (e := 0) (f := 8) s₁ s₂ hperm (by decide) (by omega)
      (by omega) rfl (Option.mem_def.mpr rfl) hj₂ hj₃ roseJunctionRefute_endC5a
  · rw [hw] at hperm hj₃
    exact roseJunctionRefute_tail (e := 0) (f := 12) s₁ s₂ hperm (by decide) (by omega)
      (by omega) rfl (Option.mem_def.mpr rfl) hj₂ hj₃ roseJunctionRefute_endC5b

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf
