import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketClosedWalkNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# The four inputs of a noncrossing pocket region, from first turns

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of
`Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`PocketRegion.ofNoncrossingClosedWalk` takes four inputs for a walk that can touch itself at a
vertex: the walk is noncrossing, the exterior face lies off the walk's side, the reversed walk
follows the boundary of the other side, and the reclosed map of the walk's side has the Euler
characteristic of the map.  This module produces all four from one condition on the complement
spelling `c` of the pocket, the walk being `c.reverse.map alpha`.

The condition is that `c` is a list of distinct darts using no edge in both directions, and each
dart reaches the next, and the last dart the first, by a first turn (`FirstTurn`): rotating from
its reversal, past darts off the edges of `c`.

* `FirstTurnWalk.isNoncrossingClosedWalk`: `c` is a noncrossing closed walk.
* `IsNoncrossingClosedWalk.reverseMapAlpha`: the reversed walk of a noncrossing closed walk is
  noncrossing.  It is the outer boundary cycle, so this is `BoundaryCycle.isNoncrossingClosedWalk`
  (`Estimating/OsinPocketClosedWalkNoncrossing.lean`).
* `FirstTurnWalk.outerCycle_followsBoundary`: the outer cycle of the reversed walk is `c`, and it
  follows its boundary.  The darts a first turn rotates past lie off the walk, and the face class
  of a dart of `c` never meets the walk's side (`IsNoncrossingClosedWalk.not_faceClass_alpha`), so
  those darts are internal to the other side.
* `FirstTurnWalk.not_mem_sideFaces`: a face on the side of `c` is off the side of the reversed walk.
* The Euler equality is `IsNoncrossingClosedWalk.reclosed_euler`
  (`NoncrossingClosedWalkEuler.lean`), given the outer cycle follows.
* `FirstTurnWalkPocketInputsStatement`, `firstTurnWalkPocketInputs`: the four inputs.
* `PocketRegion.ofFirstTurnWalk`: the pocket region, with complement cycle `c`.
* Producers of first turns: `FirstTurn.of_sigma_alpha` (one rotation step, e.g. a face step),
  `FirstTurn.of_sigma_sigma_alpha` (two steps past a dart off the walk), `FirstTurn.of_boundaryWalk`
  (a boundary walk of a face set whose boundary darts include `c`), and `FirstTurn.mono`.

The model tests are in `Estimating/OsinPocketFirstTurnWalkModel.lean`: the pinched two-gon, the
lake, and a pendant spur.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv Surgery.MapCollapse SimpleClosedWalkSides

universe u w v

/-- **A first turn** from `x` to `y` along the edges of `c`: rotating `k > 0` steps from the
reversal `alpha x` reaches `y`, and every earlier step is a dart off the edges of `c`. -/
def FirstTurn (M : CombMap.{u}) (c : List M.Dart) (x y : M.Dart) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (M.sigma ^ k) (M.alpha x) = y ∧
    ∀ t, 0 < t → t < k → ¬ walkKeep M c ((M.sigma ^ t) (M.alpha x))

namespace FirstTurnWalk

/-- Rotation preserves the vertex of a dart. -/
theorem vertexOf_sigma_pow (M : CombMap.{u}) (n : ℕ) (d : M.Dart) :
    M.vertexOf ((M.sigma ^ n) d) = M.vertexOf d := by
  induction n with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.vertexOf_sigma, ih]

/-- In a list chained by `R` and closed by `R` from its last to its first element, every element
has a successor in the list. -/
theorem exists_mem_rel_of_isChain {α : Type*} {R : α → α → Prop} {l : List α}
    (hne : l ≠ []) (hchain : l.IsChain R) (hclose : R (l.getLast hne) (l.head hne))
    {a : α} (ha : a ∈ l) : ∃ b ∈ l, R a b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  by_cases hlast : i + 1 < l.length
  · exact ⟨l[i + 1], List.getElem_mem hlast, List.isChain_iff_getElem.mp hchain i (by omega)⟩
  · refine ⟨l.head hne, List.head_mem hne, ?_⟩
    have hgl : l[i] = l.getLast hne := by
      rw [List.getLast_eq_getElem]
      congr 1
      omega
    rw [hgl]
    exact hclose

variable {M : CombMap.{u}}

theorem mem_reverse_map_alpha_iff {c : List M.Dart} {d : M.Dart} :
    d ∈ c.reverse.map M.alpha ↔ M.alpha d ∈ c := by
  rw [List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [M.alpha_involutive e]
    exact List.mem_reverse.mp he
  · intro hd
    exact ⟨M.alpha d, List.mem_reverse.mpr hd, M.alpha_involutive d⟩

/-- A walk and its reversed walk use the same edges. -/
theorem walkKeep_reverse_map_alpha (c : List M.Dart) :
    walkKeep M (c.reverse.map M.alpha) = walkKeep M c := by
  funext d
  apply propext
  unfold walkKeep
  rw [mem_reverse_map_alpha_iff, mem_reverse_map_alpha_iff, M.alpha_involutive d]
  exact Or.comm

/-- Reversing a walk twice gives the walk back. -/
theorem reverse_map_alpha_involutive (c : List M.Dart) :
    (c.reverse.map M.alpha).reverse.map M.alpha = c := by
  simp only [List.map_reverse, List.reverse_reverse, List.map_map,
    M.alpha_involutive.comp_self, List.map_id]

/-- The face of a dart of `c` lies on the side of `c`. -/
theorem faceOf_mem_sideFaces {c : List M.Dart} {d : M.Dart} (hd : d ∈ c) :
    M.faceOf d ∈ sideFaces M c :=
  (mem_sideFaces_iff M c d).mpr ⟨d, hd, .refl _⟩

/-- An internal dart of a face set lies off the edges of a list of its boundary darts. -/
theorem not_walkKeep_of_internalDart {c : List M.Dart} {faces : Finset M.Face}
    (hbd : ∀ d ∈ c, IsBoundaryDart M faces d) {z : M.Dart} (hz : InternalDart M faces z) :
    ¬ walkKeep M c z := by
  obtain ⟨hz1, hz2⟩ := hz
  rintro (hmem | hmem)
  · obtain ⟨-, hout⟩ := hbd z hmem
    exact hout hz2
  · obtain ⟨-, hout⟩ := hbd _ hmem
    rw [M.alpha_involutive z] at hout
    exact hout hz1

end FirstTurnWalk

namespace FirstTurn

variable {M : CombMap.{u}} {c : List M.Dart} {x y : M.Dart}

/-- One rotation step from the reversal is a first turn. -/
theorem of_sigma_alpha (h : M.sigma (M.alpha x) = y) : FirstTurn M c x y :=
  ⟨1, Nat.zero_lt_one, by rw [pow_one]; exact h, fun _ ht htk => absurd htk (by omega)⟩

/-- A face step is a first turn. -/
theorem of_facePerm (h : M.facePerm x = y) : FirstTurn M c x y :=
  of_sigma_alpha h

/-- Two rotation steps from the reversal, past a dart off the edges of `c`, are a first turn. -/
theorem of_sigma_sigma_alpha (hz : ¬ walkKeep M c (M.sigma (M.alpha x)))
    (h : M.sigma (M.sigma (M.alpha x)) = y) : FirstTurn M c x y := by
  refine ⟨2, Nat.zero_lt_two, by rw [pow_two, Perm.mul_apply]; exact h, fun t ht htk => ?_⟩
  obtain rfl : t = 1 := by omega
  rw [pow_one]
  exact hz

/-- A boundary walk of a face set whose boundary darts include `c` is a first turn: the darts it
rotates past are internal, so they lie off the edges of `c`. -/
theorem of_boundaryWalk {faces : Finset M.Face} (hbd : ∀ d ∈ c, IsBoundaryDart M faces d)
    (h : BoundaryWalk M faces x y) : FirstTurn M c x y := by
  obtain ⟨n, hn, hskip⟩ :=
    PermFirstReturn.exists_pow_of_skip_walk M.sigma (InternalDart M faces) h
  refine ⟨n + 1, Nat.succ_pos n, ?_, fun t ht htn => ?_⟩
  · rw [pow_succ, Perm.mul_apply]
    exact hn
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ, Perm.mul_apply]
    exact FirstTurnWalk.not_walkKeep_of_internalDart hbd (hskip s (by omega))

/-- A first turn along the edges of `c` is one along the edges of any `c'` whose edges are edges
of `c`. -/
theorem mono {c' : List M.Dart} (hkeep : ∀ z, walkKeep M c' z → walkKeep M c z)
    (h : FirstTurn M c x y) : FirstTurn M c' x y := by
  obtain ⟨k, hk, hky, havoid⟩ := h
  exact ⟨k, hk, hky, fun t ht htk hz => havoid t ht htk (hkeep _ hz)⟩

/-- A first turn stays at one vertex. -/
theorem vertexOf_eq (h : FirstTurn M c x y) : M.vertexOf (M.alpha x) = M.vertexOf y := by
  obtain ⟨k, -, rfl, -⟩ := h
  exact (FirstTurnWalk.vertexOf_sigma_pow M k (M.alpha x)).symm

end FirstTurn

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **The reversed walk of a noncrossing closed walk is noncrossing.**  It is the outer boundary
cycle, so this is `BoundaryCycle.isNoncrossingClosedWalk`. -/
theorem reverseMapAlpha (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar) :
    IsNoncrossingClosedWalk M (w.reverse.map M.alpha) := by
  refine (hw.outerCycle hM).isNoncrossingClosedWalk ?_ ?_
  · show (w.reverse.map M.alpha).IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e
    rw [List.isChain_map, List.isChain_reverse]
    refine hw.chain.imp_of_mem_imp fun a b _ _ h => ?_
    show M.vertexOf (M.alpha (M.alpha b)) = M.vertexOf (M.alpha a)
    rw [M.alpha_involutive b]
    exact h.symm
  · show M.vertexOf (M.alpha ((w.reverse.map M.alpha).getLast _)) =
      M.vertexOf ((w.reverse.map M.alpha).head _)
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    rw [M.alpha_involutive]
    exact hw.closes.symm

end IsNoncrossingClosedWalk

namespace FirstTurnWalk

variable {M : CombMap.{u}} {c : List M.Dart}

/-- **A first-turn walk is noncrossing**: a nonempty list of distinct darts using no edge in both
directions, in which each dart reaches the next, and the last the first, by a first turn. -/
theorem isNoncrossingClosedWalk (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, M.alpha x ∉ c) (hchain : c.IsChain (FirstTurn M c))
    (hclose : FirstTurn M c (c.getLast hne) (c.head hne)) : IsNoncrossingClosedWalk M c where
  ne_nil := hne
  nodup := hnodup
  chain := hchain.imp_of_mem_imp fun _ _ _ _ h => h.vertexOf_eq
  closes := hclose.vertexOf_eq
  alpha_not_mem := halpha
  turn_mem d hd := by
    obtain ⟨y, hy, k, hk, hky, havoid⟩ := exists_mem_rel_of_isChain hne hchain hclose hd
    exact NoncrossingClosedWalkSides.turn_mem_of_first hk (by rw [hky]; exact hy) havoid

/-- The reversed walk of a first-turn walk is noncrossing. -/
theorem isNoncrossingClosedWalk_reverse (hM : M.IsPlanar) (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, M.alpha x ∉ c) (hchain : c.IsChain (FirstTurn M c))
    (hclose : FirstTurn M c (c.getLast hne) (c.head hne)) :
    IsNoncrossingClosedWalk M (c.reverse.map M.alpha) :=
  (isNoncrossingClosedWalk hne hnodup halpha hchain hclose).reverseMapAlpha hM

/-- A first turn along `c` from a dart of `c` is a boundary walk of the other side of the reversed
walk: the darts it rotates past lie off the walk, and their face class never meets the walk. -/
theorem boundaryWalk_of_firstTurn (hM : M.IsPlanar)
    (hw : IsNoncrossingClosedWalk M (c.reverse.map M.alpha)) {a b : M.Dart} (ha : a ∈ c)
    (h : FirstTurn M c a b) : BoundaryWalk M (sideOutside M (c.reverse.map M.alpha)) a b := by
  obtain ⟨k, hk, rfl, havoid⟩ := h
  refine boundaryWalk_of_run M (walkKeep M (c.reverse.map M.alpha)) _ a hk ?_ ?_
  · intro t ht htk
    rw [walkKeep_reverse_map_alpha]
    exact havoid t ht htk
  · intro x hx
    rw [mem_sideOutside_iff, mem_sideFaces_iff]
    rintro ⟨d, hd, hdx⟩
    have hmem : M.alpha a ∈ c.reverse.map M.alpha :=
      List.mem_map.mpr ⟨a, List.mem_reverse.mpr ha, rfl⟩
    refine hw.not_faceClass_alpha hM hd hmem ?_
    rw [M.alpha_involutive a]
    exact .trans _ _ _ hdx (.symm _ _ hx)

/-- **The outer cycle follows its boundary.**  The outer cycle of the reversed walk is `c`, and
each first turn of `c` is a boundary walk of the other side. -/
theorem outerCycle_followsBoundary (hM : M.IsPlanar) (hchain : c.IsChain (FirstTurn M c))
    (hne : c ≠ []) (hclose : FirstTurn M c (c.getLast hne) (c.head hne))
    (hw : IsNoncrossingClosedWalk M (c.reverse.map M.alpha)) :
    (hw.outerCycle hM).FollowsBoundary := by
  refine BoundaryCycle.followsBoundary_of_chain _ ?_ ?_
  · show ((c.reverse.map M.alpha).reverse.map M.alpha).IsChain
      (BoundaryWalk M (sideOutside M (c.reverse.map M.alpha)))
    rw [reverse_map_alpha_involutive]
    exact hchain.imp_of_mem_imp fun _ _ ha _ h => boundaryWalk_of_firstTurn hM hw ha h
  · show BoundaryWalk M (sideOutside M (c.reverse.map M.alpha))
      (((c.reverse.map M.alpha).reverse.map M.alpha).getLast _)
      (((c.reverse.map M.alpha).reverse.map M.alpha).head _)
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    rw [M.alpha_involutive, M.alpha_involutive]
    exact boundaryWalk_of_firstTurn hM hw (List.getLast_mem hne) hclose

/-- **A face on the side of `c` is off the side of the reversed walk.** -/
theorem not_mem_sideFaces (hM : M.IsPlanar)
    (hw : IsNoncrossingClosedWalk M (c.reverse.map M.alpha)) {f : M.Face}
    (hf : f ∈ sideFaces M c) : f ∉ sideFaces M (c.reverse.map M.alpha) := by
  revert hf
  refine Quotient.inductionOn' f ?_
  intro x hf
  change M.faceOf x ∈ sideFaces M c at hf
  change M.faceOf x ∉ sideFaces M (c.reverse.map M.alpha)
  rw [mem_sideFaces_iff] at hf ⊢
  obtain ⟨d, hd, hdx⟩ := hf
  rintro ⟨e, he, hex⟩
  have hmem : M.alpha d ∈ c.reverse.map M.alpha :=
    List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩
  refine hw.not_faceClass_alpha hM he hmem ?_
  rw [M.alpha_involutive d]
  rw [walkKeep_reverse_map_alpha] at hex ⊢
  exact .trans _ _ _ hex (.symm _ _ hdx)

end FirstTurnWalk

/-- **The four inputs of a noncrossing pocket region, from first turns.**  On a planar map, let
`c` be a nonempty list of distinct darts using no edge in both directions, in which each dart
reaches the next, and the last the first, by a first turn along `c`.  Then the reversed walk
`c.reverse.map alpha` is noncrossing, every face on the side of `c` is off its side, its outer
cycle follows its boundary, and the reclosed map of its side has the Euler characteristic of the
map. -/
def FirstTurnWalkPocketInputsStatement : Prop :=
  ∀ (M : CombMap.{u}) (hM : M.IsPlanar) (c : List M.Dart) (hne : c ≠ []), c.Nodup →
    (∀ x ∈ c, M.alpha x ∉ c) → c.IsChain (FirstTurn M c) →
      FirstTurn M c (c.getLast hne) (c.head hne) →
      ∃ hw : IsNoncrossingClosedWalk M (c.reverse.map M.alpha),
        (∀ f ∈ sideFaces M c, f ∉ sideFaces M (c.reverse.map M.alpha)) ∧
          (hw.outerCycle hM).FollowsBoundary ∧
          (reclosedMap M (sideFaces M (c.reverse.map M.alpha))
            (hw.innerCycle hM)).eulerCharacteristic = M.eulerCharacteristic

theorem firstTurnWalkPocketInputs : FirstTurnWalkPocketInputsStatement.{u} := by
  intro M hM c hne hnodup halpha hchain hclose
  have hw := FirstTurnWalk.isNoncrossingClosedWalk_reverse hM hne hnodup halpha hchain hclose
  have hfollows := FirstTurnWalk.outerCycle_followsBoundary hM hchain hne hclose hw
  exact ⟨hw, fun _ hf => FirstTurnWalk.not_mem_sideFaces hM hw hf, hfollows,
    hw.reclosed_euler hM hfollows⟩

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {c : List Delta.toCombMap.Dart}

/-- **The pocket region of a first-turn walk** `c` whose side holds the exterior face: the faces
on the side of the reversed walk.  Its complement cycle is `c`. -/
noncomputable def ofFirstTurnWalk (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) : PocketRegion Delta :=
  have hw := FirstTurnWalk.isNoncrossingClosedWalk_reverse Delta.planar hne hnodup halpha
    hchain hclose
  have hfollows := FirstTurnWalk.outerCycle_followsBoundary Delta.planar hchain hne hclose hw
  ofNoncrossingClosedWalk hw (FirstTurnWalk.not_mem_sideFaces Delta.planar hw hout) hfollows
    (hw.reclosed_euler Delta.planar hfollows)

theorem ofFirstTurnWalk_faces (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) :
    (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).faces =
      sideFaces Delta.toCombMap (c.reverse.map Delta.toCombMap.alpha) :=
  rfl

theorem ofFirstTurnWalk_inner_cycle (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) :
    (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).inner.cycle =
      c.reverse.map Delta.toCombMap.alpha :=
  rfl

/-- The complement cycle of the pocket is `c`. -/
theorem ofFirstTurnWalk_outer_cycle (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) :
    (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).outer.cycle = c :=
  FirstTurnWalk.reverse_map_alpha_involutive c

/-- The inverse complement cycle of the pocket is the reversed walk. -/
theorem ofFirstTurnWalk_invDarts_outer (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) :
    Embedded.invDarts Delta (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).outer.cycle =
      c.reverse.map Delta.toCombMap.alpha :=
  invDarts_reverse_map_alpha _

/-- The face across a dart of `c` is inside the pocket. -/
theorem faceOf_alpha_mem_ofFirstTurnWalk_faces (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) {d : Delta.toCombMap.Dart}
    (hd : d ∈ c) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) ∈
      (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).faces :=
  FirstTurnWalk.faceOf_mem_sideFaces (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)

/-- The face of a dart of `c` is outside the pocket. -/
theorem faceOf_not_mem_ofFirstTurnWalk_faces (hne : c ≠ []) (hnodup : c.Nodup)
    (halpha : ∀ x ∈ c, Delta.toCombMap.alpha x ∉ c)
    (hchain : c.IsChain (FirstTurn Delta.toCombMap c))
    (hclose : FirstTurn Delta.toCombMap c (c.getLast hne) (c.head hne))
    (hout : Delta.outerFace ∈ sideFaces Delta.toCombMap c) {d : Delta.toCombMap.Dart}
    (hd : d ∈ c) :
    Delta.toCombMap.faceOf d ∉ (ofFirstTurnWalk hne hnodup halpha hchain hclose hout).faces :=
  FirstTurnWalk.not_mem_sideFaces Delta.planar
    (FirstTurnWalk.isNoncrossingClosedWalk_reverse Delta.planar hne hnodup halpha hchain hclose)
    (FirstTurnWalk.faceOf_mem_sideFaces hd)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurn.of_boundaryWalk
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.reverseMapAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.isNoncrossingClosedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.outerCycle_followsBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.FirstTurnWalk.not_mem_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.ofFirstTurnWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.faceOf_not_mem_ofFirstTurnWalk_faces
#audit_closed_axioms GroupApproximation.GGT.VanKampen.firstTurnWalkPocketInputs
