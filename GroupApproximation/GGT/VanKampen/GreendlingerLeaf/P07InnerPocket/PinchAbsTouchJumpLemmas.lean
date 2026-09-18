import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PinchAbsTouchArcLemmas
import GroupApproximation.GGT.VanKampen.FaceSetCircuitNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-83: the local shape of a pinched unkept jump

Let `c` be a boundary circuit of a face set `H` (a `FaceSetCircuits.circuit`), `G` a dart list and
`Kw` a noncrossing closed walk with `alpha e ∈ G → e ∈ Kw`.

* `pinchAbsTouchJump_walk_of_rotate`: two darts `x, y` adjacent in a rotation of `c` are joined by
  a `BoundaryWalk` of `H` (`circuit_chain`, `circuit_closes`).
* `pinchAbsTouchJump_Wedge M H Kw G c x y`: the **wedge** of a pinched unkept jump from `x` to `y`.
  Both lie in `G`, `x` is pinched, `facePerm x` is not kept by `c`, and `y = σ^(n+1) (α x)` with
  `n ≥ 1` and every dart `σ^k (α x)`, `1 ≤ k ≤ n`, internal to `H`.  If moreover `facePerm x ∈ G`,
  some wedge dart `σ^k (α x)` with `1 < k ≤ n` is a dart of `Kw`.
* `pinchAbsTouchJump_wedge_of_walk`: every pinched unkept pair `x, y` of `G` joined by a
  `BoundaryWalk` of `H`, with `y ∈ c`, has this wedge.  `n ≥ 1` since `n = 0` gives
  `y = facePerm x`, which is then kept.  The `Kw` dart comes from the first kept dart after
  `facePerm x` around the vertex (`PocketRun.exists_firstKeep`, `turn_mem`): it comes no later than
  `y` (whose reverse is in `Kw`) and is not `y` (as `y ∉ Kw`).
* `pinchAbsTouchJump_Free M H Kw G c`: no wedge between adjacent darts, in the two regimes of
  `pinchAbsTouchArc_Run`.
* `pinchAbsTouchJump_run_of_free`: `pinchAbsTouchJump_Free` gives `pinchAbsTouchArc_Run M G c`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe v

open SimpleClosedWalkSides Surgery.MapCollapse

/-- Both members of an adjacent pair of a rotation are members of the list. -/
theorem pinchAbsTouchJump_mem_of_rotate {α : Type*} {l : List α} {m : ℕ} {S Q : List α}
    {x y : α} (h : l.rotate m = S ++ x :: y :: Q) : x ∈ l ∧ y ∈ l := by
  have hx : x ∈ l.rotate m := by
    rw [h]
    simp
  have hy : y ∈ l.rotate m := by
    rw [h]
    simp
  exact ⟨List.mem_rotate.mp hx, List.mem_rotate.mp hy⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_mem_of_rotate

/-- **Adjacent circuit darts are joined by a boundary walk.** -/
theorem pinchAbsTouchJump_walk_of_rotate (M : CombMap.{v}) (H : Finset M.Face)
    (comp : FaceSetCircuits.Component M H) {m : ℕ} {S Q : List M.Dart} {x y : M.Dart}
    (h : (FaceSetCircuits.circuit M H comp).rotate m = S ++ x :: y :: Q) :
    BoundaryWalk M H x y := by
  obtain ⟨k, hk, hx, hy⟩ := pinchAbsTouchArc_exists_idx h
  subst hx hy
  exact GroupApproximation.GGT.VanKampen.PolygonList.rel_getElem_mod
    (FaceSetCircuits.circuit_nonempty M H comp) (FaceSetCircuits.circuit_chain M H comp)
    (FaceSetCircuits.circuit_closes M H comp) k hk

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_walk_of_rotate

/-- Rotating from the reverse of the reverse of `facePerm x` is rotating from `α x`, one step on. -/
theorem pinchAbsTouchJump_pow_facePerm (M : CombMap.{v}) (x : M.Dart) (m : ℕ) :
    (M.sigma ^ m) (M.alpha (M.alpha (M.facePerm x))) = (M.sigma ^ (m + 1)) (M.alpha x) := by
  rw [M.alpha_involutive (M.facePerm x), PocketRun.facePerm_eq_sigma_alpha,
    pow_succ M.sigma m, Equiv.Perm.mul_apply]

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_pow_facePerm

/-- **The wedge of a pinched unkept jump** from `x` to `y` (see the module docstring). -/
def pinchAbsTouchJump_Wedge (M : CombMap.{v}) (H : Finset M.Face) (Kw G c : List M.Dart)
    (x y : M.Dart) : Prop :=
  x ∈ G ∧ y ∈ G ∧ ¬ PocketRun.PinchFreeAt M x ∧ ¬ walkKeep M c (M.facePerm x) ∧
    ∃ n : ℕ, 0 < n ∧ (M.sigma ^ (n + 1)) (M.alpha x) = y ∧
      (∀ k, 0 < k → k ≤ n → InternalDart M H ((M.sigma ^ k) (M.alpha x))) ∧
      (M.facePerm x ∈ G → ∃ k, 1 < k ∧ k ≤ n ∧ (M.sigma ^ k) (M.alpha x) ∈ Kw)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_Wedge

/-- **Every pinched unkept pair joined by a boundary walk has the wedge.** -/
theorem pinchAbsTouchJump_wedge_of_walk (M : CombMap.{v}) {H : Finset M.Face}
    {Kw G c : List M.Dart} {x y : M.Dart} (hxy : BoundaryWalk M H x y) (hyc : y ∈ c)
    (hxG : x ∈ G) (hyG : y ∈ G) (hpf : ¬ PocketRun.PinchFreeAt M x)
    (hkeep : ¬ walkKeep M c (M.facePerm x)) (hnc : IsNoncrossingClosedWalk M Kw)
    (hKw : ∀ e, M.alpha e ∈ G → e ∈ Kw) :
    pinchAbsTouchJump_Wedge M H Kw G c x y := by
  obtain ⟨n, hn, hint⟩ := Surgery.MapCollapse.BoundaryWalk.exists_pow hxy
  have hn0 : 0 < n := by
    refine Nat.pos_of_ne_zero fun h0 => hkeep ?_
    subst h0
    have h1 : M.facePerm x = y := by
      rw [PocketRun.facePerm_eq_sigma_alpha, ← hn, Nat.zero_add, pow_one]
    rw [h1]
    exact Or.inl hyc
  unfold pinchAbsTouchJump_Wedge
  refine ⟨hxG, hyG, hpf, hkeep, n, hn0, hn, hint, fun hfG => ?_⟩
  have hd : M.alpha (M.facePerm x) ∈ Kw :=
    hKw (M.alpha (M.facePerm x)) (by rw [M.alpha_involutive (M.facePerm x)]; exact hfG)
  have hαy : M.alpha y ∈ Kw := hKw (M.alpha y) (by rw [M.alpha_involutive y]; exact hyG)
  have hyK : y ∉ Kw := by
    have h2 := hnc.alpha_not_mem (M.alpha y) hαy
    rwa [M.alpha_involutive y] at h2
  obtain ⟨m, hm0, hmk, hmin⟩ := PocketRun.exists_firstKeep Kw hd
  have hmem := hnc.turn_mem (M.alpha (M.facePerm x)) hd m hm0 hmk hmin
  rw [pinchAbsTouchJump_pow_facePerm] at hmem
  have hmn : m ≤ n := by
    by_contra hlt
    refine hmin n hn0 (by omega) ?_
    rw [pinchAbsTouchJump_pow_facePerm, hn]
    exact Or.inr hαy
  have hne : m ≠ n := by
    rintro rfl
    rw [hn] at hmem
    exact hyK hmem
  exact ⟨m + 1, by omega, by omega, hmem⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_wedge_of_walk

/-- **No wedge between adjacent darts.**  (i) If some dart of `c` is off `G`, no two adjacent
darts of `c` (read cyclically) have the wedge.  (ii) If `c` lies inside `G`, no two adjacent darts
of one rotation of `c` (not read cyclically) have it. -/
def pinchAbsTouchJump_Free (M : CombMap.{v}) (H : Finset M.Face) (Kw G c : List M.Dart) :
    Prop :=
  ((∃ e ∈ c, e ∉ G) → ∀ (m : ℕ) (S Q : List M.Dart) (x y : M.Dart),
      c.rotate m = S ++ x :: y :: Q → ¬ pinchAbsTouchJump_Wedge M H Kw G c x y) ∧
  ((∀ e ∈ c, e ∈ G) → ∃ n : ℕ, ∀ (S Q : List M.Dart) (x y : M.Dart),
      c.rotate n = S ++ x :: y :: Q → ¬ pinchAbsTouchJump_Wedge M H Kw G c x y)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_Free

/-- **No wedge gives the run predicate along the circuit.** -/
theorem pinchAbsTouchJump_run_of_free (M : CombMap.{v}) (H : Finset M.Face)
    (comp : FaceSetCircuits.Component M H) {Kw G : List M.Dart}
    (hnc : IsNoncrossingClosedWalk M Kw) (hKw : ∀ e, M.alpha e ∈ G → e ∈ Kw)
    (h : pinchAbsTouchJump_Free M H Kw G (FaceSetCircuits.circuit M H comp)) :
    pinchAbsTouchArc_Run M G (FaceSetCircuits.circuit M H comp) := by
  unfold pinchAbsTouchArc_Run
  refine ⟨fun hoff m S Q x y hr hxG hyG hpf hkeep => ?_, fun hall => ?_⟩
  · exact absurd (pinchAbsTouchJump_wedge_of_walk M (pinchAbsTouchJump_walk_of_rotate M H comp hr)
      (pinchAbsTouchJump_mem_of_rotate hr).2 hxG hyG hpf hkeep hnc hKw) (h.1 hoff m S Q x y hr)
  · obtain ⟨n, hn⟩ := h.2 hall
    refine ⟨n, fun S Q x y hr hpf hkeep => ?_⟩
    have hmem := pinchAbsTouchJump_mem_of_rotate hr
    exact absurd (pinchAbsTouchJump_wedge_of_walk M (pinchAbsTouchJump_walk_of_rotate M H comp hr)
      hmem.2 (hall x hmem.1) (hall y hmem.2) hpf hkeep hnc hKw) (hn S Q x y hr)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.pinchAbsTouchJump_run_of_free

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
