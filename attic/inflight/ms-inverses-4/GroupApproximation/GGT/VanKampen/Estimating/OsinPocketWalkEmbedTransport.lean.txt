import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# A tight closed walk across a dart embedding

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell: the touch-only X-pocket.
Before a touch vertex is split, both pocket corners are thickened (`OsinPocketTouchCornerStatement`,
`Estimating/OsinPocketTouchSplitStatements.lean`).  The thickened copy comes with a dart map `e` that
is injective, commutes with edge reversal, keeps labels, reflects and preserves vertices, and keeps
vertex rotation away from the corners of the two entering darts `in₁` and `in₂`.  This module
carries the invariants of the pocket walk across such a map:

* `walkKeep_map_iff`: a dart is on the mapped walk or reverses one exactly when its preimage is;
* `tightTurn_map` and `isTightClosedWalk_map`: tight turns stay tight.  Every dart of a tight stretch
  before its end is the next walk dart or off the walk, so it is not `alpha in₁` or `alpha in₂`, and
  its successor is off the walk or is `alpha d`, which is not `in₁` or `in₂` on a walk with no spur;
* `nodup_map_vertexOf_map` and `repeatedVisits_map_le`: vertex repetitions do not grow;
* `dartWord_map`: words are unchanged.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides

namespace WalkSplit

section Embed

variable {M M' : CombMap.{v}} {e : M.Dart → M'.Dart}

/-- **Keeping a dart is reflected by the embedding.** -/
theorem walkKeep_map_iff (he : Function.Injective e)
    (halpha : ∀ d, M'.alpha (e d) = e (M.alpha d)) {walk : List M.Dart} (z : M.Dart) :
    walkKeep M' (walk.map e) (e z) ↔ walkKeep M walk z := by
  unfold walkKeep
  rw [halpha, List.mem_map_of_injective he, List.mem_map_of_injective he]

/-- **A tight turn stays tight across the embedding**, on a walk with no spur through the two
entering darts. -/
theorem tightTurn_map (he : Function.Injective e)
    (halpha : ∀ d, M'.alpha (e d) = e (M.alpha d)) {walk : List M.Dart} {in₁ in₂ : M.Dart}
    (hin₁ : in₁ ∈ walk) (hin₂ : in₂ ∈ walk) (hspur : ∀ d ∈ walk, M.alpha d ∉ walk)
    (hsigma : ∀ d, d ≠ M.alpha in₁ → d ≠ M.alpha in₂ → M.sigma d ≠ in₁ → M.sigma d ≠ in₂ →
      M'.sigma (e d) = e (M.sigma d))
    {d f : M.Dart} (hd : d ∈ walk) (hf : f ∈ walk) (h : TightTurn M walk d f) :
    TightTurn M' (walk.map e) (e d) (e f) := by
  obtain ⟨n, hn, hnk⟩ := h
  have hz : ∀ k < n, (M.sigma ^ k) f ≠ M.alpha in₁ ∧ (M.sigma ^ k) f ≠ M.alpha in₂ ∧
      M.sigma ((M.sigma ^ k) f) ≠ in₁ ∧ M.sigma ((M.sigma ^ k) f) ≠ in₂ := by
    intro k hk
    have hsucc : M.sigma ((M.sigma ^ k) f) = (M.sigma ^ (k + 1)) f := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    have hnot_succ : ∀ j ∈ walk, M.sigma ((M.sigma ^ k) f) ≠ j := by
      intro j hj hsj
      rcases Nat.lt_or_ge (k + 1) n with hlt | hge
      · exact hnk (k + 1) (Nat.succ_pos k) hlt (by rw [← hsucc, hsj]; exact Or.inl hj)
      · have hkn : k + 1 = n := by omega
        rw [hsucc, hkn, hn] at hsj
        exact hspur d hd (by rw [hsj]; exact hj)
    have hnot_start : ∀ j ∈ walk, (M.sigma ^ k) f ≠ M.alpha j := by
      intro j hj hzj
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero, Equiv.Perm.one_apply] at hzj
        exact hspur j hj (by rw [← hzj]; exact hf)
      · exact hnk k hkpos hk (by rw [hzj]; exact Or.inr (by rw [M.alpha_involutive]; exact hj))
    exact ⟨hnot_start in₁ hin₁, hnot_start in₂ hin₂, hnot_succ in₁ hin₁, hnot_succ in₂ hin₂⟩
  have hpow : ∀ k ≤ n, (M'.sigma ^ k) (e f) = e ((M.sigma ^ k) f) := by
    intro k
    induction k with
    | zero => intro _; simp only [pow_zero, Equiv.Perm.one_apply]
    | succ k ih =>
        intro hk
        rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega), pow_succ', Equiv.Perm.mul_apply]
        obtain ⟨h₁, h₂, h₃, h₄⟩ := hz k (by omega)
        exact hsigma _ h₁ h₂ h₃ h₄
  refine ⟨n, ?_, fun k hk hkn => ?_⟩
  · rw [hpow n le_rfl, hn, halpha]
  · rw [hpow k hkn.le, walkKeep_map_iff he halpha]
    exact hnk k hk hkn

/-- **A tight closed walk stays tight across the embedding.** -/
theorem isTightClosedWalk_map (he : Function.Injective e)
    (halpha : ∀ d, M'.alpha (e d) = e (M.alpha d)) {walk : List M.Dart}
    (hw : IsTightClosedWalk M walk) {in₁ in₂ : M.Dart} (hin₁ : in₁ ∈ walk) (hin₂ : in₂ ∈ walk)
    (hsigma : ∀ d, d ≠ M.alpha in₁ → d ≠ M.alpha in₂ → M.sigma d ≠ in₁ → M.sigma d ≠ in₂ →
      M'.sigma (e d) = e (M.sigma d)) :
    IsTightClosedWalk M' (walk.map e) where
  ne_nil := by simpa using hw.ne_nil
  chain := by
    rw [List.isChain_map]
    exact hw.chain.imp_of_mem_imp fun _ _ ha hb h =>
      tightTurn_map he halpha hin₁ hin₂ hw.alpha_not_mem hsigma ha hb h
  closes := by
    rw [List.getLast_map, List.head_map]
    exact tightTurn_map he halpha hin₁ hin₂ hw.alpha_not_mem hsigma (List.getLast_mem _)
      (List.head_mem _) hw.closes
  alpha_not_mem := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    rw [halpha, List.mem_map_of_injective he]
    exact hw.alpha_not_mem a ha

/-- A map on vertices back along the embedding, defined on the image. -/
theorem exists_vertex_pull
    (hvert : ∀ d d', M'.vertexOf (e d) = M'.vertexOf (e d') ↔ M.vertexOf d = M.vertexOf d')
    (d₀ : M.Dart) : ∃ φ : M'.Vertex → M.Vertex, ∀ a, φ (M'.vertexOf (e a)) = M.vertexOf a := by
  classical
  refine ⟨fun u => if h : ∃ a, M'.vertexOf (e a) = u then M.vertexOf (Classical.choose h)
    else M.vertexOf d₀, fun a => ?_⟩
  dsimp only
  split_ifs with h
  · exact (hvert _ _).mp (Classical.choose_spec h)
  · exact absurd ⟨a, rfl⟩ h

/-- **A list that repeats no vertex repeats none after the embedding.** -/
theorem nodup_map_vertexOf_map
    (hvert : ∀ d d', M'.vertexOf (e d) = M'.vertexOf (e d') ↔ M.vertexOf d = M.vertexOf d')
    {l : List M.Dart} (h : (l.map M.vertexOf).Nodup) : ((l.map e).map M'.vertexOf).Nodup := by
  rcases l with _ | ⟨d₀, t⟩
  · simp
  · obtain ⟨φ, hφ⟩ := exists_vertex_pull hvert d₀
    refine List.Nodup.of_map φ ?_
    rw [List.map_map, List.map_map]
    have hcomp : φ ∘ (M'.vertexOf ∘ e) = M.vertexOf := funext hφ
    rw [hcomp]
    exact h

/-- **The repeated visits do not grow across the embedding.** -/
theorem repeatedVisits_map_le
    (hvert : ∀ d d', M'.vertexOf (e d) = M'.vertexOf (e d') ↔ M.vertexOf d = M.vertexOf d')
    (walk : List M.Dart) : repeatedVisits M' (walk.map e) ≤ repeatedVisits M walk := by
  rcases walk with _ | ⟨d₀, t⟩
  · simp [repeatedVisits]
  · obtain ⟨φ, hφ⟩ := exists_vertex_pull hvert d₀
    unfold repeatedVisits
    rw [List.length_map, List.map_map]
    exact length_sub_card_toFinset_map_le (fun a => M'.vertexOf (e a)) φ M.vertexOf hφ _

end Embed

/-- **Words are unchanged across a label-keeping dart map.** -/
theorem dartWord_map {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {X X' : DiscDiagram.{u, w, v} W} {e : X.toCombMap.Dart → X'.toCombMap.Dart}
    (hlabel : ∀ d, X'.label (e d) = X.label d) (l : List X.toCombMap.Dart) :
    dartWord X' (l.map e) = dartWord X l := by
  unfold dartWord
  rw [List.map_map]
  exact List.map_congr_left fun d _ => hlabel d

end WalkSplit

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.tightTurn_map
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.isTightClosedWalk_map
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.nodup_map_vertexOf_map
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.repeatedVisits_map_le
#audit_axioms GroupApproximation.GGT.VanKampen.WalkSplit.dartWord_map
