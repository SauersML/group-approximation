import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchSplit
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchStep
import GroupApproximation.Meta.AxiomGuard

/-!
# A vertex splitting keeps walk order and lowers repeated visits

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A pocket face set in walk order that passes twice through a vertex is
split there (`PocketFaceSet.pinchSplit`).  The boundary cycle stays in walk order when each step of
vertex rotation between consecutive darts meets neither split dart before its end, and the
repeated visits drop when two darts of the cycle land on the two new vertices.  A pocket in walk
order with no repeated vertex is simple.

* `PinchSplit.Input.StretchAvoids` and `vertexOf_eq_of_stretchAvoids`: a stretch of vertex
  rotation that meets neither split dart before its end stays in one vertex after the split.
* `PinchSplit.Input.stretchAvoids_of_vertexOf_ne`: away from the split vertex every stretch
  avoids the split darts.
* `PocketFaceSet.pinchSplit_closedWalk`: the split pocket is in walk order.
* `PocketFaceSet.pinchSplit_repeatedVisits_le`, `pinchSplit_repeatedVisits_lt` and
  `pinchSplit_repeatedVisits_lt_of_stretch`: the repeated visits do not increase, and they drop when
  two darts of the cycle land on the new vertices of `x` and `y`.
* `PocketFaceSet.repeatedVisits_eq_zero_iff`, `simple_of_closedWalk_of_vertex_nodup` and
  `simple_of_closedWalk_of_repeatedVisits_eq_zero`: a pocket in walk order with no repeated vertex
  is simple.

## Manuscript status

Infrastructure for `thm:hull` (tex 1903,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- Along a stretch of `p` that meets neither `a` nor `b` before its end, composing with the
transposition of `a` and `b` changes nothing. -/
private theorem mul_swap_pow_apply_of_avoids {α : Type*} [DecidableEq α] (p : Equiv.Perm α)
    (a b d : α) :
    ∀ n : ℕ, (∀ i < n, (p ^ i) d ≠ a ∧ (p ^ i) d ≠ b) →
      ((p * Equiv.swap a b) ^ n) d = (p ^ n) d := by
  intro n
  induction n with
  | zero =>
      intro _
      simp only [pow_zero]
  | succ n ih =>
      intro h
      have hn := h n (Nat.lt_succ_self n)
      rw [pow_succ', Equiv.Perm.mul_apply, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hn.1 hn.2, pow_succ',
        Equiv.Perm.mul_apply]

/-! ## Distinct values along a list -/

/-- **Coarser values repeat at least as often.**  If `g` factors through `f`, a list has at least
as many repeats under `g` as under `f`. -/
theorem length_sub_card_toFinset_map_le {α β γ : Type*} {_ : DecidableEq β}
    {_ : DecidableEq γ} (f : α → β) (φ : β → γ) (g : α → γ) (hφ : ∀ a, φ (f a) = g a)
    (l : List α) : l.length - (l.map f).toFinset.card ≤ l.length - (l.map g).toFinset.card := by
  have hsub : (l.map g).toFinset ⊆ (l.map f).toFinset.image φ := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact Finset.mem_image.mpr ⟨f d, List.mem_toFinset.mpr (List.mem_map_of_mem hd), hφ d⟩
  exact Nat.sub_le_sub_left ((Finset.card_le_card hsub).trans Finset.card_image_le) _

/-- **Merging two values repeats strictly more often.**  If `g` factors through `f` and merges the
values of `f` at two entries of the list, the list has strictly more repeats under `g` than under
`f`. -/
theorem length_sub_card_toFinset_map_lt {α β γ : Type*} {_ : DecidableEq β}
    {_ : DecidableEq γ} (f : α → β) (φ : β → γ) (g : α → γ) (hφ : ∀ a, φ (f a) = g a)
    {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hf : f a ≠ f b) (hg : g a = g b) :
    l.length - (l.map f).toFinset.card < l.length - (l.map g).toFinset.card := by
  have hmem : ∀ c ∈ l, f c ∈ (l.map f).toFinset := fun c hc =>
    List.mem_toFinset.mpr (List.mem_map_of_mem hc)
  have hsub : (l.map g).toFinset ⊆ (l.map f).toFinset.image φ := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact Finset.mem_image.mpr ⟨f d, hmem d hd, hφ d⟩
  have hne : ((l.map f).toFinset.image φ).card ≠ (l.map f).toFinset.card := fun h =>
    hf (Finset.card_image_iff.mp h (Finset.mem_coe.mpr (hmem a ha))
      (Finset.mem_coe.mpr (hmem b hb)) ((hφ a).trans (hg.trans (hφ b).symm)))
  have hlt : ((l.map f).toFinset.image φ).card < (l.map f).toFinset.card :=
    lt_of_le_of_ne Finset.card_image_le hne
  have hle : (l.map g).toFinset.card ≤ ((l.map f).toFinset.image φ).card :=
    Finset.card_le_card hsub
  have hlen : (l.map f).toFinset.card ≤ l.length :=
    (List.toFinset_card_le _).trans_eq (List.length_map f)
  omega

/-- **No repeats means no duplicate values.** -/
theorem length_sub_card_toFinset_map_eq_zero_iff {α β : Type*} {_ : DecidableEq β} (f : α → β)
    (l : List α) : l.length - (l.map f).toFinset.card = 0 ↔ (l.map f).Nodup := by
  have hle : (l.map f).toFinset.card ≤ l.length :=
    (List.toFinset_card_le _).trans_eq (List.length_map f)
  constructor
  · intro h
    have hcard : ((l.map f : List β) : Multiset β).toFinset.card =
        Multiset.card ((l.map f : List β) : Multiset β) := by
      change (l.map f).toFinset.card = (l.map f).length
      rw [List.length_map]
      omega
    exact Multiset.coe_nodup.mp (Multiset.toFinset_card_eq_card_iff_nodup.mp hcard)
  · intro h
    rw [List.toFinset_card_of_nodup h, List.length_map, Nat.sub_self]

namespace PinchSplit.Input

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} [DecidableEq Delta.toCombMap.Dart] (I : Input Delta)

/-! ## Stretches of vertex rotation -/

/-- A stretch of vertex rotation from `d` to `e` that meets neither split dart before its end. -/
def StretchAvoids (d e : Delta.toCombMap.Dart) : Prop :=
  ∃ n : ℕ, (Delta.toCombMap.sigma ^ n) d = e ∧
    ∀ i < n, (Delta.toCombMap.sigma ^ i) d ≠ I.x ∧ (Delta.toCombMap.sigma ^ i) d ≠ I.y

/-- **A stretch that avoids the split darts stays in one cycle of vertex rotation after the
split.** -/
theorem sameCycle_of_stretchAvoids {d e : Delta.toCombMap.Dart} (h : I.StretchAvoids d e) :
    I.diagram.toCombMap.sigma.SameCycle d e := by
  obtain ⟨n, hn, havoid⟩ := h
  have hpow : ((Delta.toCombMap.sigma * Equiv.swap I.x I.y) ^ n) d = e :=
    (mul_swap_pow_apply_of_avoids Delta.toCombMap.sigma I.x I.y d n havoid).trans hn
  have hsc : (Delta.toCombMap.sigma * Equiv.swap I.x I.y).SameCycle d e :=
    ⟨n, by rw [zpow_natCast]; exact hpow⟩
  exact hsc

/-- **A stretch that avoids the split darts stays in one vertex after the split.** -/
theorem vertexOf_eq_of_stretchAvoids {d e : Delta.toCombMap.Dart} (h : I.StretchAvoids d e) :
    I.diagram.toCombMap.vertexOf d = I.diagram.toCombMap.vertexOf e :=
  (I.diagram.toCombMap.vertexOf_eq_iff d e).mpr (I.sameCycle_of_stretchAvoids h)

/-- **Away from the split vertex every stretch avoids the split darts.** -/
theorem stretchAvoids_of_vertexOf_ne {d e : Delta.toCombMap.Dart}
    (h : Delta.toCombMap.vertexOf d = Delta.toCombMap.vertexOf e)
    (hne : Delta.toCombMap.vertexOf d ≠ Delta.toCombMap.vertexOf I.x) : I.StretchAvoids d e := by
  obtain ⟨n, hn⟩ := ((Delta.toCombMap.vertexOf_eq_iff d e).mp h).exists_nat_pow_eq
  refine ⟨n, hn, fun i _ => ⟨fun hx => hne ?_, fun hy => hne ?_⟩⟩
  · exact (Delta.toCombMap.vertexOf_eq_iff d I.x).mpr ⟨i, by rw [zpow_natCast]; exact hx⟩
  · exact (Delta.toCombMap.vertexOf_eq_iff d I.x).mpr
      (Equiv.Perm.SameCycle.trans ⟨i, by rw [zpow_natCast]; exact hy⟩ I.same_vertex.symm)

/-! ## Vertices before and after -/

/-- The old vertex containing a new vertex. -/
def vertexProj : I.diagram.toCombMap.Vertex → Delta.toCombMap.Vertex :=
  Quotient.lift Delta.toCombMap.vertexOf fun a b hab =>
    I.vertexOf_eq_of_diagram ((I.diagram.toCombMap.vertexOf_eq_iff a b).mpr hab)

theorem vertexProj_vertexOf (d : Delta.toCombMap.Dart) :
    I.vertexProj (I.diagram.toCombMap.vertexOf d) = Delta.toCombMap.vertexOf d :=
  rfl

end PinchSplit.Input

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-! ## No repeated vertex -/

/-- **The repeated visits vanish exactly when no vertex repeats.** -/
theorem repeatedVisits_eq_zero_iff (K : PocketFaceSet D eps X lo hi) :
    K.repeatedVisits = 0 ↔ (K.boundary.cycle.map X.toCombMap.vertexOf).Nodup := by
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_eq_zero_iff X.toCombMap.vertexOf K.boundary.cycle

/-- **A pocket in walk order with no repeated vertex is simple.**  A boundary cycle never holds
both darts of an edge. -/
theorem simple_of_closedWalk_of_vertex_nodup (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (hnodup : (K.boundary.cycle.map X.toCombMap.vertexOf).Nodup) :
    K.Simple :=
  (⟨K.boundary.cycle_nonempty, hK.1, hK.2, hnodup, fun _ hd had =>
    ((K.boundary.cycle_mem_iff _).mp hd).2 ((K.boundary.cycle_mem_iff _).mp had).1⟩ :
    IsSimpleClosedWalk X.toCombMap K.boundary.cycle)

/-- **A pocket in walk order with no repeated visits is simple.** -/
theorem simple_of_closedWalk_of_repeatedVisits_eq_zero (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (h : K.repeatedVisits = 0) : K.Simple :=
  K.simple_of_closedWalk_of_vertex_nodup hK (K.repeatedVisits_eq_zero_iff.mp h)

variable [DecidableEq X.toCombMap.Dart]

/-! ## Across the split -/

/-- **The split pocket is in walk order** when each step between consecutive darts of the
boundary cycle, and the closing step, runs along vertex rotation without meeting a split dart
before its end. -/
theorem pinchSplit_closedWalk (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.StretchAvoids (X.toCombMap.alpha d) e)
    (hcloses : I.StretchAvoids
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty)) :
    (K.pinchSplit I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_stretchAvoids h,
    I.vertexOf_eq_of_stretchAvoids hcloses⟩

/-- **The split does not increase the repeated visits.** -/
theorem pinchSplit_repeatedVisits_le (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) : (K.pinchSplit I hs).repeatedVisits ≤ K.repeatedVisits := by
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_le I.diagram.toCombMap.vertexOf I.vertexProj
    X.toCombMap.vertexOf I.vertexProj_vertexOf K.boundary.cycle

/-- **The split lowers the repeated visits** when two darts of the boundary cycle land on the new
vertices of `x` and `y`. -/
theorem pinchSplit_repeatedVisits_lt (K : PocketFaceSet D eps X lo hi) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle)
    (he₂ : e₂ ∈ K.boundary.cycle)
    (hx : I.diagram.toCombMap.vertexOf e₁ = I.diagram.toCombMap.vertexOf I.x)
    (hy : I.diagram.toCombMap.vertexOf e₂ = I.diagram.toCombMap.vertexOf I.y) :
    (K.pinchSplit I hs).repeatedVisits < K.repeatedVisits := by
  have hne : I.diagram.toCombMap.vertexOf e₁ ≠ I.diagram.toCombMap.vertexOf e₂ := fun h =>
    I.vertexOf_x_ne_y (hx.symm.trans (h.trans hy))
  have heq : X.toCombMap.vertexOf e₁ = X.toCombMap.vertexOf e₂ :=
    (I.vertexOf_eq_of_diagram hx).trans
      (((X.toCombMap.vertexOf_eq_iff I.x I.y).mpr I.same_vertex).trans
        (I.vertexOf_eq_of_diagram hy).symm)
  unfold PocketFaceSet.repeatedVisits
  exact length_sub_card_toFinset_map_lt I.diagram.toCombMap.vertexOf I.vertexProj
    X.toCombMap.vertexOf I.vertexProj_vertexOf he₁ he₂ hne heq

/-- **The split lowers the repeated visits**, from stretches of vertex rotation: one dart of the
boundary cycle runs into `x` without passing `y`, and another runs into `y` without passing
`x`. -/
theorem pinchSplit_repeatedVisits_lt_of_stretch (K : PocketFaceSet D eps X lo hi)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces) {e₁ e₂ : X.toCombMap.Dart}
    (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle) {n₁ n₂ : ℕ}
    (hn₁ : (X.toCombMap.sigma ^ n₁) e₁ = I.x)
    (hy₁ : ∀ i ≤ n₁, (X.toCombMap.sigma ^ i) e₁ ≠ I.y)
    (hn₂ : (X.toCombMap.sigma ^ n₂) e₂ = I.y)
    (hx₂ : ∀ i ≤ n₂, (X.toCombMap.sigma ^ i) e₂ ≠ I.x) :
    (K.pinchSplit I hs).repeatedVisits < K.repeatedVisits :=
  K.pinchSplit_repeatedVisits_lt I hs he₁ he₂
    ((I.diagram.toCombMap.vertexOf_eq_iff e₁ I.x).mpr (I.sameCycle_x_of_stretch hn₁ hy₁))
    ((I.diagram.toCombMap.vertexOf_eq_iff e₂ I.y).mpr (I.sameCycle_y_of_stretch hn₂ hx₂))

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.length_sub_card_toFinset_map_le
#audit_axioms GroupApproximation.GGT.VanKampen.length_sub_card_toFinset_map_lt
#audit_axioms GroupApproximation.GGT.VanKampen.length_sub_card_toFinset_map_eq_zero_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.StretchAvoids
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.sameCycle_of_stretchAvoids
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexOf_eq_of_stretchAvoids
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.stretchAvoids_of_vertexOf_ne
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexProj
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.vertexProj_vertexOf
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.repeatedVisits_eq_zero_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.simple_of_closedWalk_of_vertex_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.simple_of_closedWalk_of_repeatedVisits_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_closedWalk
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_repeatedVisits_le
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_repeatedVisits_lt
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.pinchSplit_repeatedVisits_lt_of_stretch
