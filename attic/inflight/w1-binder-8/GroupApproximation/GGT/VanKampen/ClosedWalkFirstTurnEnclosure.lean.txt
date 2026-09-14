import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketFirstTurnWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The faces enclosed by a closed walk that may run along bridges

A closed dart walk turns like a noncrossing walk when, rotating from the reversal of a walk dart, the
first dart met on an edge of the walk is a walk dart (`FirstTurnEnclosure.TurnMem`).  Unlike a
noncrossing closed walk, such a walk may use both darts of an edge: a bridge.  This module separates
the two sides of such a walk in a planar map.

* `FirstTurnEnclosure.walkMap_facePerm_mem` and `walkMap_connected`: the map on the edges of the walk
  is connected, and its face rotation keeps walk darts on the walk.  These are the arguments of
  `IsNoncrossingClosedWalk.walkMap_facePerm_mem` and `walkMap_connected`, which never use that no
  edge is used in both directions.
* `FirstTurnEnclosure.alpha_mem_of_faceClass` (separation): advancing around faces and crossing
  edges off the walk, a walk dart reaches the reversal of a walk dart only when that reversal is a
  walk dart.
* `enclosedFaces`: the faces reached from the reversals of the walk darts whose reversal is off the
  walk, without crossing an edge of the walk.
* `FirstTurnEnclosure.mem_iff_enclosedFaces`: a dart is a walk dart exactly when it is based off the
  enclosed faces, and either its reversal is based in them or the reversal is a walk dart.  This is
  the field `mem_iff` of `EnclosedFaceSet`.
* `FirstTurnEnclosure.turnMem_of_firstTurn`, `eq_of_firstTurn` and `firstTurn_getElem_succ`: a walk
  chained by first turns (`FirstTurn`) turns like a noncrossing walk, and the first dart on an edge of
  the walk after the reversal of a walk dart is the next walk dart (the field `turn_next` of
  `EnclosedFaceSetSucc`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u

open scoped Classical in
/-- **The enclosed faces of a closed walk**: the faces reached from the reversal of a walk dart whose
reversal is off the walk, advancing around faces and crossing edges off the walk. -/
noncomputable def enclosedFaces (M : CombMap.{u}) (c : List M.Dart) : Finset M.Face :=
  Finset.univ.filter fun g => ∃ x, M.faceOf x = g ∧
    ∃ a ∈ c, M.alpha a ∉ c ∧
      Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha a) x

namespace FirstTurnEnclosure

theorem mem_enclosedFaces_iff (M : CombMap.{u}) (c : List M.Dart) (x : M.Dart) :
    M.faceOf x ∈ enclosedFaces M c ↔
      ∃ a ∈ c, M.alpha a ∉ c ∧
        Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) (M.alpha a) x := by
  classical
  unfold enclosedFaces
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, y, hy, a, ha, hna, h⟩
    exact ⟨a, ha, hna, .trans _ _ _ h
      (eqvGen_faceClass_of_sameCycle M _ ((M.faceOf_eq_iff y x).mp hy))⟩
  · rintro ⟨a, ha, hna, h⟩
    exact ⟨Finset.mem_univ _, x, rfl, a, ha, hna, h⟩

/-- **The turning condition** of a closed walk: rotating from the reversal of a walk dart, the first
dart met on an edge of the walk is a walk dart. -/
abbrev TurnMem (M : CombMap.{u}) (c : List M.Dart) : Prop :=
  ∀ d ∈ c, ∀ m : ℕ, 0 < m → walkKeep M c ((M.sigma ^ m) (M.alpha d)) →
    (∀ k, 0 < k → k < m → ¬ walkKeep M c ((M.sigma ^ k) (M.alpha d))) →
    (M.sigma ^ m) (M.alpha d) ∈ c

variable {M : CombMap.{u}} {c : List M.Dart}

theorem alpha_keep {a : M.Dart} (ha : a ∈ c) : walkKeep M c (M.alpha a) :=
  Or.inr (by rw [M.alpha_involutive a]; exact ha)

/-- The restricted face permutation sends walk darts to walk darts. -/
theorem walkMap_facePerm_mem (hturn : TurnMem M c) (d : (walkMap M c).Dart) (hd : d.1 ∈ c) :
    ((walkMap M c).facePerm d).1 ∈ c := by
  obtain ⟨m, hm, hpm, havoid⟩ :=
    (walkMap_isRestriction M c).sigma_firstReturn ⟨M.alpha d.1, alpha_keep hd⟩
  obtain ⟨z, hz, hzd⟩ : ∃ z : (walkMap M c).Dart,
      (M.sigma ^ m) (M.alpha d.1) = z.1 ∧ (walkMap M c).facePerm d = z :=
    ⟨(walkMap M c).sigma ⟨M.alpha d.1, alpha_keep hd⟩, hpm, rfl⟩
  rw [hzd, ← hz]
  refine hturn d.1 hd m hm ?_ fun k hk0 hkm hkeep => havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩
  rw [hz]
  exact z.2

/-- The map on the edges of a closed walk is connected. -/
theorem walkMap_connected (hne : c ≠ [])
    (hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e) :
    (walkMap M c).IsConnected := by
  have hmem : ∀ x ∈ c, ∃ hx : walkKeep M c x, Relation.EqvGen (walkMap M c).Adjacent
      ⟨c.head hne, Or.inl (List.head_mem hne)⟩ ⟨x, hx⟩ := by
    refine List.IsChain.induction (fun x => ∃ hx : walkKeep M c x,
      Relation.EqvGen (walkMap M c).Adjacent
        ⟨c.head hne, Or.inl (List.head_mem hne)⟩ ⟨x, hx⟩)
      c (List.IsChain.iff_mem.mp hchain) ?_ ?_
    · rintro x y ⟨hxw, hyw, hxy⟩ ⟨hx, h⟩
      refine ⟨Or.inl hyw, Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.trans _ ⟨M.alpha x, alpha_keep hxw⟩ _
          (Relation.EqvGen.rel _ _ (Or.inl rfl))
          (NoncrossingClosedWalkSides.eqvGen_adjacent_of_sameCycle _ ?_))⟩
      exact (PermFirstReturn.sameCycle_iff _ _ _ (walkMap_isRestriction M c).sigma_firstReturn
        _ _).mpr ((M.vertexOf_eq_iff _ _).mp hxy)
    · intro lne
      exact ⟨Or.inl (List.head_mem lne), Relation.EqvGen.refl _⟩
  have hall : ∀ x : (walkMap M c).Dart, Relation.EqvGen (walkMap M c).Adjacent
      ⟨c.head hne, Or.inl (List.head_mem hne)⟩ x := by
    rintro ⟨x, hx | hx⟩
    · obtain ⟨_, h⟩ := hmem x hx
      exact h
    · obtain ⟨_, h⟩ := hmem _ hx
      exact Relation.EqvGen.trans _ _ _ h
        (Relation.EqvGen.rel _ _ (Or.inl (Subtype.ext (M.alpha_involutive x))))
  intro d e
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hall d)) (hall e)

/-- **Separation.**  Advancing around ambient faces and crossing edges off the walk, a walk dart
reaches the reversal of a walk dart only when that reversal is a walk dart. -/
theorem alpha_mem_of_faceClass (hM : M.IsPlanar) (hne : c ≠ [])
    (hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hturn : TurnMem M c) {a d : M.Dart} (hd : d ∈ c) (ha : a ∈ c)
    (h : Relation.EqvGen (CombMap.FaceClassStep M (walkKeep M c)) d (M.alpha a)) :
    M.alpha a ∈ c := by
  have h' : Relation.EqvGen
      (CombMap.FaceClassStep M (· ∈ Set.range (Function.Embedding.subtype (walkKeep M c))))
      d (M.alpha a) :=
    faceClass_mono M (fun x hx => by rintro ⟨z, rfl⟩; exact hx z.2) h
  have hface := (walkMap_isRestriction M c).faceOf_eq_of_faceClass hM
    (walkMap_connected hne hchain) (d := ⟨d, Or.inl hd⟩) (d' := ⟨M.alpha a, alpha_keep ha⟩) h'
  obtain ⟨n, hn⟩ := (((walkMap M c).faceOf_eq_iff _ _).mp hface).exists_nat_pow_eq
  have hpow : ∀ m : ℕ, (((walkMap M c).facePerm ^ m) ⟨d, Or.inl hd⟩).1 ∈ c := by
    intro m
    induction m with
    | zero => exact hd
    | succ m ih =>
        rw [pow_succ', Perm.mul_apply]
        exact walkMap_facePerm_mem hturn _ ih
  have hmem := hpow n
  rw [hn] at hmem
  exact hmem

/-- Crossing an edge off the walk keeps the enclosed faces. -/
theorem faceOf_alpha_mem_enclosedFaces {x : M.Dart} (hkeep : ¬ walkKeep M c x)
    (hx : M.faceOf x ∈ enclosedFaces M c) : M.faceOf (M.alpha x) ∈ enclosedFaces M c := by
  obtain ⟨a, ha, hna, h⟩ := (mem_enclosedFaces_iff M c x).mp hx
  exact (mem_enclosedFaces_iff M c _).mpr
    ⟨a, ha, hna, .trans _ _ _ h (.rel _ _ (Or.inr ⟨hkeep, rfl⟩))⟩

/-- **The boundary of the enclosed faces.**  A dart is a walk dart exactly when it is based off the
enclosed faces, and either its reversal is based in them or the reversal is a walk dart. -/
theorem mem_iff_enclosedFaces (hM : M.IsPlanar) (hne : c ≠ [])
    (hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hturn : TurnMem M c) (d : M.Dart) :
    d ∈ c ↔ M.faceOf d ∉ enclosedFaces M c ∧
      (M.faceOf (M.alpha d) ∈ enclosedFaces M c ∨ M.alpha d ∈ c) := by
  constructor
  · intro hd
    refine ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨a, ha, hna, h⟩ := (mem_enclosedFaces_iff M c d).mp hmem
      exact hna (alpha_mem_of_faceClass hM hne hchain hturn hd ha (.symm _ _ h))
    · by_cases hα : M.alpha d ∈ c
      · exact Or.inr hα
      · exact Or.inl ((mem_enclosedFaces_iff M c _).mpr ⟨d, hd, hα, .refl _⟩)
  · rintro ⟨hnot, hor⟩
    by_contra hd
    have hseed : M.alpha d ∈ c → False := fun hα => hnot ((mem_enclosedFaces_iff M c d).mpr
      ⟨M.alpha d, hα, by rwa [M.alpha_involutive d], by rw [M.alpha_involutive d]; exact .refl _⟩)
    rcases hor with hF | hα
    · refine hnot ?_
      have hkeep : ¬ walkKeep M c (M.alpha d) := by
        rintro (h₁ | h₂)
        · exact hseed h₁
        · rw [M.alpha_involutive d] at h₂
          exact hd h₂
      have h := faceOf_alpha_mem_enclosedFaces hkeep hF
      rwa [M.alpha_involutive d] at h
    · exact hseed hα

/-- A face holding a walk dart is not enclosed. -/
theorem faceOf_not_mem_enclosedFaces (hM : M.IsPlanar) (hne : c ≠ [])
    (hchain : c.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hturn : TurnMem M c) {d : M.Dart} (hd : d ∈ c) : M.faceOf d ∉ enclosedFaces M c :=
  ((mem_iff_enclosedFaces hM hne hchain hturn d).mp hd).1

/-- **A walk chained by first turns turns like a noncrossing walk.** -/
theorem turnMem_of_firstTurn (hne : c ≠ []) (hchain : c.IsChain (FirstTurn M c))
    (hclose : FirstTurn M c (c.getLast hne) (c.head hne)) : TurnMem M c := by
  intro d hd
  obtain ⟨y, hy, k, hk, hky, havoid⟩ :=
    FirstTurnWalk.exists_mem_rel_of_isChain hne hchain hclose hd
  exact NoncrossingClosedWalkSides.turn_mem_of_first hk (by rw [hky]; exact hy) havoid

/-- **The first kept dart is the target of the first turn.** -/
theorem eq_of_firstTurn {x y : M.Dart} (h : FirstTurn M c x y) (hy : y ∈ c) {m : ℕ} (hm : 0 < m)
    (hkeep : walkKeep M c ((M.sigma ^ m) (M.alpha x)))
    (hfirst : ∀ k, 0 < k → k < m → ¬ walkKeep M c ((M.sigma ^ k) (M.alpha x))) :
    (M.sigma ^ m) (M.alpha x) = y := by
  obtain ⟨k, hk, hky, havoid⟩ := h
  rcases lt_trichotomy m k with hlt | rfl | hgt
  · exact absurd hkeep (havoid m hm hlt)
  · exact hky
  · exact absurd (by rw [hky]; exact Or.inl hy) (hfirst k hk hgt)

/-- **A walk chained by first turns turns to its successor**, at list positions.  The walk is named
`l` here, since `c[…]` is Mathlib's literal notation for `Cycle`. -/
theorem firstTurn_getElem_succ {l : List M.Dart} (hne : l ≠ [])
    (hchain : l.IsChain (FirstTurn M l)) (hclose : FirstTurn M l (l.getLast hne) (l.head hne))
    {i : ℕ} (hi : i < l.length) (hj : (i + 1) % l.length < l.length) :
    FirstTurn M l l[i] l[(i + 1) % l.length] := by
  by_cases h1 : i + 1 < l.length
  · have e : l[(i + 1) % l.length] = l[i + 1] := by
      simp only [Nat.mod_eq_of_lt h1]
    rw [e]
    exact List.isChain_iff_getElem.mp hchain i h1
  · have hgl : l[i] = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    have hmod : (i + 1) % l.length = 0 := by
      rw [show i + 1 = l.length by omega, Nat.mod_self]
    have hhead : l[(i + 1) % l.length] = l.head hne := by
      simp only [hmod, List.head_eq_getElem]
    rw [hgl, hhead]
    exact hclose

end FirstTurnEnclosure

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.mem_enclosedFaces_iff
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.walkMap_facePerm_mem
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.walkMap_connected
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.alpha_mem_of_faceClass
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.mem_iff_enclosedFaces
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.turnMem_of_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.eq_of_firstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnEnclosure.firstTurn_getElem_succ
