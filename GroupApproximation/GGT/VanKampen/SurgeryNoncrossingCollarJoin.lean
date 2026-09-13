import GroupApproximation.GGT.VanKampen.SurgeryNoncrossingCollarStrip
import GroupApproximation.Meta.AxiomGuard

/-!
# The corner join of a noncrossing strip

`GeodesicCollar.Strip.join_walk` joins the end vertices of the side `p` of a strip at
`x = alpha (q.getLast)` and `y = alpha (p.getLast)`, and reads off from `vertex_nodup` that the rest
`r` is a simple closed walk of the join.  Over a noncrossing walk the two corners can lie at one
vertex (`NoncrossingCollarJoinModels.pinchedJoinModel`).  This module shows that when they do not,
the rest is a noncrossing closed walk of the join whose outer cycle follows its boundary.

* `pow_vertexJoin_eq`: before the first dart kept by the walk, the joined rotation agrees with the
  old one, unless the old rotation reaches `p.head` through `x`.
* `outerTurn_vertexJoin_rest`: the rest turns back in the join.  The last dart of the rest turns
  back through `y` and `p.head` to the head of the rest.
* `exists_first_mem_vertexJoin_rest`: rotating from the reversal of a dart of the rest, the join
  first meets a dart of the rest.  When the old rotation meets `x`, the join goes on from
  `sigma y` along the rotation of `y`, which does not contain `x`.
* `isNoncrossingClosedWalk_vertexJoin_rest`, and `NoncrossingStrip.join_walk` for a strip.

No vertex of the walk needs to be visited only once, and no inner boundary condition is used.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin

open Equiv SimpleClosedWalkSides NoncrossingCollarWalk

universe u

/-- A member of a chain other than its head follows some member of the chain. -/
theorem exists_rel_of_mem {α : Type*} {R : α → α → Prop} {l : List α} (hl : l.IsChain R)
    (hne : l ≠ []) {e : α} (he : e ∈ l) (hhead : e ≠ l.head hne) : ∃ e' ∈ l, R e' e := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · exact (hhead rfl).elim
    · have hl' := List.isChain_cons.mp hl
      by_cases hel : e = l.head (List.ne_nil_of_mem he')
      · exact ⟨a, List.mem_cons_self, by rw [hel]; exact hl'.1 _ (List.head_mem_head? _)⟩
      · obtain ⟨e', he'l, h⟩ := ih hl'.2 (List.ne_nil_of_mem he') he' hel
        exact ⟨e', List.mem_cons_of_mem a he'l, h⟩

section Join

variable {M : CombMap.{u}} [DecidableEq M.Dart] {p r : List M.Dart} {x y : M.Dart}

omit [DecidableEq M.Dart] in
/-- A dart kept by the rest is kept by the walk. -/
theorem walkKeep_append_right {z : M.Dart} (h : walkKeep M r z) : walkKeep M (p ++ r) z :=
  Or.imp (List.mem_append_right p) (List.mem_append_right p) h

/-- Before the first dart kept by the walk, the joined rotation from `z` agrees with the old
rotation, unless the old rotation reaches `p.head` through `x`. -/
theorem pow_vertexJoin_eq (hp : p ≠ []) (hσx : M.sigma x = p.head hp)
    (hy : M.alpha y = p.getLast hp) {z : M.Dart} {m : ℕ} (hzy : z ≠ y)
    (havoid : ∀ k, 0 < k → k < m → ¬ walkKeep M (p ++ r) ((M.sigma ^ k) z))
    (hhead : (M.sigma ^ m) z ≠ p.head hp) :
    ∀ k, k ≤ m → ((VertexJoin.toCombMap M x y).sigma ^ k) z = (M.sigma ^ k) z := by
  intro k hkm
  refine pow_mul_swap_apply M.sigma x y z k fun j hj => ⟨fun hjx => ?_, fun hjy => ?_⟩
  · have hsucc : (M.sigma ^ (j + 1)) z = p.head hp := by
      rw [pow_succ', Perm.mul_apply, hjx, hσx]
    rcases Nat.lt_or_ge (j + 1) m with hlt | hge
    · exact havoid (j + 1) (Nat.succ_pos j) hlt
        (Or.inl (by rw [hsucc]; exact List.mem_append_left r (List.head_mem hp)))
    · exact hhead (by rw [show m = j + 1 by omega]; exact hsucc)
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Perm.one_apply] at hjy
      exact hzy hjy
    · exact havoid j hj0 (by omega)
        (Or.inr (by rw [hjy, hy]; exact List.mem_append_left r (List.getLast_mem hp)))

/-- A walk dart turns back to a walk dart before it in the join, rotating past neither `x` nor
`y`. -/
theorem turnsBack_vertexJoin_rest (hw : IsNoncrossingClosedWalk M (p ++ r)) (hp : p ≠ [])
    (hσx : M.sigma x = p.head hp) (hy : M.alpha y = p.getLast hp) {a b : M.Dart}
    (ha : a ∈ p ++ r) (hb : b ∈ p ++ r) (h : TurnsBack M (p ++ r) a b) :
    TurnsBack (VertexJoin.toCombMap M x y) r a b := by
  obtain ⟨m, hm, hpm, havoid⟩ := h
  have hpow := pow_vertexJoin_eq (r := r) (z := b) hp hσx hy
    (fun hby => hw.alpha_not_mem b hb
      (by rw [hby, hy]; exact List.mem_append_left r (List.getLast_mem hp)))
    havoid
    (fun hhead => hw.alpha_not_mem a ha
      (by rw [← hpm, hhead]; exact List.mem_append_left r (List.head_mem hp)))
  refine ⟨m, hm, by rw [hpow m le_rfl]; exact hpm, fun k hk0 hkm hkeep => havoid k hk0 hkm ?_⟩
  rw [← hpow k hkm.le]
  exact walkKeep_append_right hkeep

/-- The last dart of the rest turns back to the head of the rest in the join: the old rotation
reaches `y` from `r.head`, the join sends `y` to `p.head`, and the old rotation reaches
`alpha (r.getLast)` from `p.head`. -/
theorem turnsBack_vertexJoin_getLast_head (hw : IsNoncrossingClosedWalk M (p ++ r))
    (ht : OuterTurn M (p ++ r)) (hp : p ≠ []) (hr : r ≠ []) (hσx : M.sigma x = p.head hp)
    (hy : M.alpha y = p.getLast hp) :
    TurnsBack (VertexJoin.toCombMap M x y) r (r.getLast hr) (r.head hr) := by
  have hne : p ++ r ≠ [] := List.append_ne_nil_of_left_ne_nil hp r
  have hmemp : ∀ e ∈ p, e ∈ p ++ r := fun e he => List.mem_append_left r he
  have hmemr : ∀ e ∈ r, e ∈ p ++ r := fun e he => List.mem_append_right p he
  obtain ⟨a, ha, hpa, havoida⟩ := ht.chain.rel_getLast_head_of_append hp hr
  obtain ⟨c, hc, hpc, havoidc⟩ := ht.closes hne
  rw [List.getLast_append_of_ne_nil _ hr, List.head_append_of_ne_nil hp] at hpc
  rw [List.head_append_of_ne_nil hp] at havoidc
  have hya : (M.sigma ^ a) (r.head hr) = y := by rw [hpa, ← hy, M.alpha_involutive y]
  have hpowa := pow_vertexJoin_eq (r := r) (z := r.head hr) (m := a) hp hσx hy
    (fun h => hw.alpha_not_mem _ (hmemr _ (List.head_mem hr))
      (by rw [h, hy]; exact hmemp _ (List.getLast_mem hp)))
    havoida
    (fun h => hw.alpha_not_mem _ (hmemp _ (List.getLast_mem hp))
      (by rw [← hpa, h]; exact hmemp _ (List.head_mem hp)))
  have hpowc := pow_vertexJoin_eq (r := r) (z := p.head hp) (m := c) hp hσx hy
    (fun h => hw.alpha_not_mem _ (hmemp _ (List.head_mem hp))
      (by rw [h, hy]; exact hmemp _ (List.getLast_mem hp)))
    havoidc
    (fun h => hw.alpha_not_mem _ (hmemr _ (List.getLast_mem hr))
      (by rw [← hpc, h]; exact hmemp _ (List.head_mem hp)))
  have hstep : ((VertexJoin.toCombMap M x y).sigma ^ (a + 1)) (r.head hr) = p.head hp := by
    rw [pow_succ', Perm.mul_apply, hpowa a le_rfl, hya]
    show M.sigma (swap x y y) = p.head hp
    rw [swap_apply_right, hσx]
  have hcomp : ∀ l, l ≤ c → ((VertexJoin.toCombMap M x y).sigma ^ (l + (a + 1))) (r.head hr) =
      (M.sigma ^ l) (p.head hp) := by
    intro l hl
    rw [pow_add, Perm.mul_apply, hstep, hpowc l hl]
  refine ⟨c + (a + 1), by omega, by rw [hcomp c le_rfl]; exact hpc, fun k hk0 hkm hkeep => ?_⟩
  rcases Nat.lt_or_ge k a with hka | hak
  · rw [hpowa k hka.le] at hkeep
    exact havoida k hk0 hka (walkKeep_append_right hkeep)
  rcases Nat.lt_or_ge (a + 1) k with hak' | hka'
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + (a + 1) := ⟨k - (a + 1), by omega⟩
    rw [hcomp l (by omega)] at hkeep
    exact havoidc l (by omega) (by omega) (walkKeep_append_right hkeep)
  have hnd := List.nodup_append.mp hw.nodup
  rcases Nat.lt_or_ge k (a + 1) with hka1 | hka1
  · rw [show k = a by omega, hpowa a le_rfl, hya] at hkeep
    rcases hkeep with hyr | hyr
    · exact hw.alpha_not_mem y (hmemr _ hyr) (by rw [hy]; exact hmemp _ (List.getLast_mem hp))
    · change M.alpha y ∈ r at hyr
      rw [hy] at hyr
      exact hnd.2.2 _ (List.getLast_mem hp) _ hyr rfl
  · rw [show k = a + 1 by omega, hstep] at hkeep
    rcases hkeep with hpr | hpr
    · exact hnd.2.2 _ (List.head_mem hp) _ hpr rfl
    · exact hw.alpha_not_mem _ (hmemp _ (List.head_mem hp)) (hmemr _ hpr)

/-- **The rest turns back in the join.** -/
theorem outerTurn_vertexJoin_rest (hw : IsNoncrossingClosedWalk M (p ++ r))
    (ht : OuterTurn M (p ++ r)) (hp : p ≠ []) (hσx : M.sigma x = p.head hp)
    (hy : M.alpha y = p.getLast hp) : OuterTurn (VertexJoin.toCombMap M x y) r where
  chain := ht.chain.right_of_append.imp_of_mem_imp fun _ _ ha hb h =>
    turnsBack_vertexJoin_rest hw hp hσx hy (List.mem_append_right p ha)
      (List.mem_append_right p hb) h
  closes hne := turnsBack_vertexJoin_getLast_head hw ht hp hne hσx hy

/-- **Rotating from the reversal of a dart of the rest, the join first meets a dart of the rest.**
If the old rotation first meets a dart of `p` through `x`, the join goes on from `sigma y`, and the
old rotation from `sigma y` meets neither `x` nor a dart of `p` before a walk dart. -/
theorem exists_first_mem_vertexJoin_rest (hw : IsNoncrossingClosedWalk M (p ++ r)) (hp : p ≠ [])
    (hx : ¬ walkKeep M (p ++ r) x) (hσx : M.sigma x = p.head hp) (hy : M.alpha y = p.getLast hp)
    (hσy : ¬ walkKeep M (p ++ r) (M.sigma y)) (hface : p.IsChain fun d e => M.facePerm d = e)
    (hxy : ¬ M.sigma.SameCycle x y) {d : M.Dart} (hd : d ∈ r) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ((VertexJoin.toCombMap M x y).sigma ^ m₀) (M.alpha d) ∈ r ∧
      ∀ k, 0 < k → k < m₀ →
        ¬ walkKeep M r (((VertexJoin.toCombMap M x y).sigma ^ k) (M.alpha d)) := by
  have hnd := List.nodup_append.mp hw.nodup
  have hmemp : ∀ e ∈ p, e ∈ p ++ r := fun e he => List.mem_append_left r he
  have hmemr : ∀ e ∈ r, e ∈ p ++ r := fun e he => List.mem_append_right p he
  -- The old rotation enters `p` first either at `p.head`, through `x`, or at the first step.
  have hfirst : ∀ (z : M.Dart) (n : ℕ), 0 < n → (M.sigma ^ n) z ∈ p →
      (∀ k, 0 < k → k < n → ¬ walkKeep M (p ++ r) ((M.sigma ^ k) z)) →
      (M.sigma ^ (n - 1)) z = x ∨ (n = 1 ∧ ∃ e ∈ p, z = M.alpha e) := by
    intro z n hn hmem havoid
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rw [pow_succ', Perm.mul_apply] at hmem
    by_cases hhead : M.sigma ((M.sigma ^ n') z) = p.head hp
    · exact Or.inl (M.sigma.injective (hhead.trans hσx.symm))
    · obtain ⟨e, he, hrel⟩ := exists_rel_of_mem hface hp hmem hhead
      have hrel' : M.sigma (M.alpha e) = M.sigma ((M.sigma ^ n') z) := hrel
      have hze : (M.sigma ^ n') z = M.alpha e := (M.sigma.injective hrel').symm
      rcases Nat.eq_zero_or_pos n' with rfl | hn'
      · rw [pow_zero, Perm.one_apply] at hze
        exact Or.inr ⟨rfl, e, he, hze⟩
      · exact (havoid n' hn' (by omega)
          (Or.inr (by rw [hze, M.alpha_involutive e]; exact hmemp _ he))).elim
  obtain ⟨m, hm, hmem, havoid⟩ := exists_first_mem hw (hmemr _ hd)
  have hdy : M.alpha d ≠ y := fun h =>
    hnd.2.2 _ (List.getLast_mem hp) _ hd (by rw [← hy, ← h, M.alpha_involutive d])
  by_cases hxj : ∃ j, j < m ∧ (M.sigma ^ j) (M.alpha d) = x
  swap
  · have hhead : (M.sigma ^ m) (M.alpha d) ≠ p.head hp := by
      intro h
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [pow_succ', Perm.mul_apply, ← hσx] at h
      exact hxj ⟨m', by omega, M.sigma.injective h⟩
    have hpow := pow_vertexJoin_eq (r := r) hp hσx hy hdy havoid hhead
    have hmemr' : (M.sigma ^ m) (M.alpha d) ∈ r := by
      rcases List.mem_append.mp hmem with hmp | hmr
      · rcases hfirst _ m hm hmp havoid with hx' | ⟨rfl, e, he, hde⟩
        · exact (hxj ⟨m - 1, by omega, hx'⟩).elim
        · exact (hnd.2.2 e he d hd (M.alpha_involutive.injective hde).symm).elim
      · exact hmr
    refine ⟨m, hm, by rw [hpow m le_rfl]; exact hmemr', fun k hk0 hkm hkeep =>
      havoid k hk0 hkm ?_⟩
    rw [← hpow k hkm.le]
    exact walkKeep_append_right hkeep
  obtain ⟨j, hjm, hjx⟩ := hxj
  have hjm' : j + 1 = m := by
    rcases Nat.lt_or_ge (j + 1) m with hlt | hge
    · exact (havoid (j + 1) (Nat.succ_pos j) hlt (Or.inl (by
        rw [pow_succ', Perm.mul_apply, hjx, hσx]; exact hmemp _ (List.head_mem hp)))).elim
    · omega
  subst hjm'
  have hpre := pow_vertexJoin_eq (r := r) (z := M.alpha d) (m := j) hp hσx hy hdy
    (fun k hk0 hkj => havoid k hk0 (by omega))
    (fun h => hx (by rw [← hjx, h]; exact Or.inl (hmemp _ (List.head_mem hp))))
  have hstep : ((VertexJoin.toCombMap M x y).sigma ^ (j + 1)) (M.alpha d) = M.sigma y := by
    rw [pow_succ', Perm.mul_apply, hpre j le_rfl, hjx]
    show M.sigma (swap x y x) = M.sigma y
    rw [swap_apply_left]
  obtain ⟨n, hn, hnmem, hnavoid⟩ := exists_first_mem hw (hmemp _ (List.getLast_mem hp))
  rw [← hy, M.alpha_involutive y] at hnmem hnavoid
  have hn1 : 1 < n := by
    rcases Nat.lt_or_ge 1 n with h | h
    · exact h
    · rw [show n = 1 by omega, pow_one] at hnmem
      exact (hσy (Or.inl hnmem)).elim
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hpost : ∀ l, l ≤ n' → ((VertexJoin.toCombMap M x y).sigma ^ l) (M.sigma y) =
      (M.sigma ^ (l + 1)) y := by
    intro l hln
    rw [pow_succ, Perm.mul_apply]
    refine pow_mul_swap_apply M.sigma x y (M.sigma y) l fun i hi =>
      ⟨fun hix => ?_, fun hiy => ?_⟩
    · rw [← Perm.mul_apply, ← pow_succ] at hix
      exact hxy (Perm.SameCycle.symm ⟨((i + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact hix⟩)
    · rw [← Perm.mul_apply, ← pow_succ] at hiy
      exact hnavoid (i + 1) (Nat.succ_pos i) (by omega)
        (Or.inr (by rw [hiy, hy]; exact hmemp _ (List.getLast_mem hp)))
  have hcomp : ∀ l, l ≤ n' →
      ((VertexJoin.toCombMap M x y).sigma ^ (l + (j + 1))) (M.alpha d) = (M.sigma ^ (l + 1)) y := by
    intro l hln
    rw [pow_add, Perm.mul_apply, hstep, hpost l hln]
  have hur : (M.sigma ^ (n' + 1)) y ∈ r := by
    rcases List.mem_append.mp hnmem with hup | hur
    · rcases hfirst y (n' + 1) (Nat.succ_pos n') hup hnavoid with hx' | ⟨h1, -⟩
      · rw [Nat.add_sub_cancel] at hx'
        exact (hxy (Perm.SameCycle.symm ⟨(n' : ℤ), by rw [zpow_natCast]; exact hx'⟩)).elim
      · omega
    · exact hur
  refine ⟨n' + (j + 1), by omega, by rw [hcomp n' le_rfl]; exact hur,
    fun k hk0 hkm hkeep => ?_⟩
  rcases Nat.lt_or_ge j k with hjk | hkj
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + (j + 1) := ⟨k - (j + 1), by omega⟩
    rw [hcomp l (by omega)] at hkeep
    exact hnavoid (l + 1) (Nat.succ_pos l) (by omega) (walkKeep_append_right hkeep)
  · rw [hpre k hkj] at hkeep
    exact havoid k hk0 (by omega) (walkKeep_append_right hkeep)

/-- **The rest of a noncrossing closed walk is a noncrossing closed walk of the join** at `x` and
`y`, when `sigma x` and `alpha y` are the ends of a side `p` along one face, `x` and `y` lie at
distinct vertices, and neither `x` nor `sigma y` lies on an edge of the walk. -/
theorem isNoncrossingClosedWalk_vertexJoin_rest (hw : IsNoncrossingClosedWalk M (p ++ r))
    (ht : OuterTurn M (p ++ r)) (hp : p ≠ []) (hr : r ≠ []) (hx : ¬ walkKeep M (p ++ r) x)
    (hσx : M.sigma x = p.head hp) (hy : M.alpha y = p.getLast hp)
    (hσy : ¬ walkKeep M (p ++ r) (M.sigma y)) (hface : p.IsChain fun d e => M.facePerm d = e)
    (hxy : ¬ M.sigma.SameCycle x y) :
    IsNoncrossingClosedWalk (VertexJoin.toCombMap M x y) r where
  ne_nil := hr
  nodup := (List.nodup_append.mp hw.nodup).2.1
  chain := (outerTurn_vertexJoin_rest hw ht hp hσx hy).chain.imp_of_mem_imp
    fun _ _ _ _ h => vertexOf_eq_of_turnsBack h
  closes := vertexOf_eq_of_turnsBack ((outerTurn_vertexJoin_rest hw ht hp hσx hy).closes hr)
  alpha_not_mem d hd h :=
    hw.alpha_not_mem d (List.mem_append_right p hd) (List.mem_append_right p h)
  turn_mem d hd := by
    obtain ⟨m₀, hm₀, hmem₀, havoid₀⟩ :=
      exists_first_mem_vertexJoin_rest hw hp hx hσx hy hσy hface hxy hd
    exact NoncrossingClosedWalkSides.turn_mem_of_first hm₀ hmem₀ havoid₀

end Join

#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin.exists_rel_of_mem
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin.pow_vertexJoin_eq
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin.outerTurn_vertexJoin_rest
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin.exists_first_mem_vertexJoin_rest
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin.isNoncrossingClosedWalk_vertexJoin_rest

end GroupApproximation.GGT.VanKampen.NoncrossingCollarJoin

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.NoncrossingStrip

open HullSC Surgery SimpleClosedWalkSides NoncrossingCollarWalk NoncrossingCollarJoin

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {S : Finset Delta.toCombMap.Face}
  {p r : List Delta.toCombMap.Dart} (X : NoncrossingStrip Delta S p r)

/-- The darts of the strip lie on the strip face. -/
theorem join_faceOf_eq_of_mem {e : Delta.toCombMap.Dart} (he : e ∈ p ++ X.q) :
    Delta.toCombMap.faceOf e = Delta.toCombMap.faceOf (p.head X.p_ne_nil) := by
  rw [(X.cycle.mem_iff e).mp he, List.head_append_of_ne_nil X.p_ne_nil]

/-- No crossing dart of the strip lies on an edge of the walk: it crosses from the strip face,
which lies outside `S`, into `S`. -/
theorem join_not_walkKeep {e : Delta.toCombMap.Dart} (he : e ∈ X.q) :
    ¬ walkKeep Delta.toCombMap (p ++ r) e := by
  rintro (hew | hew)
  · exact ((X.boundary e).mpr hew).2 (X.alpha_mem e he)
  · have hout := ((X.boundary _).mpr hew).2
    rw [Delta.toCombMap.alpha_involutive e,
      X.join_faceOf_eq_of_mem (List.mem_append_right p he)] at hout
    exact hout ((X.boundary _).mpr (List.mem_append_left r (List.head_mem X.p_ne_nil))).1

/-- The strip face turns from the last crossing dart to the head of the side. -/
theorem join_sigma_alpha_q :
    Delta.toCombMap.sigma (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil)) =
      p.head X.p_ne_nil := by
  have h := X.cycle.closes
  rw [List.getLast_append_of_ne_nil _ X.q_ne_nil, List.head_append_of_ne_nil X.p_ne_nil] at h
  exact h

/-- The strip face turns from the last dart of the side to the first crossing dart. -/
theorem join_sigma_alpha_p :
    Delta.toCombMap.sigma (Delta.toCombMap.alpha (p.getLast X.p_ne_nil)) =
      X.q.head X.q_ne_nil :=
  X.cycle.chain.rel_getLast_head_of_append X.p_ne_nil X.q_ne_nil

/-- The corner join of a strip is planar when its corners lie at distinct vertices. -/
theorem join_planar [DecidableEq Delta.toCombMap.Dart]
    (hxy : ¬ Delta.toCombMap.sigma.SameCycle (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil))
      (Delta.toCombMap.alpha (p.getLast X.p_ne_nil))) :
    (VertexJoin.toCombMap Delta.toCombMap (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil))
      (Delta.toCombMap.alpha (p.getLast X.p_ne_nil))).IsPlanar := by
  refine VertexJoin.planar _ _ _ Delta.planar hxy ?_ ?_
  · rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil),
      Delta.toCombMap.alpha_involutive (p.getLast X.p_ne_nil)]
    exact fun h => (List.nodup_append.mp X.cycle.nodup).2.2 _ (List.getLast_mem X.p_ne_nil) _
      (List.getLast_mem X.q_ne_nil) h.symm
  · rw [Delta.toCombMap.alpha_involutive (X.q.getLast X.q_ne_nil),
      Delta.toCombMap.alpha_involutive (p.getLast X.p_ne_nil)]
    exact (Delta.toCombMap.faceOf_eq_iff _ _).mp
      ((X.join_faceOf_eq_of_mem (List.mem_append_right p (List.getLast_mem X.q_ne_nil))).trans
        (X.join_faceOf_eq_of_mem (List.mem_append_left X.q (List.getLast_mem X.p_ne_nil))).symm)

/-- **The corner join of a noncrossing strip.**  When the corners `alpha (q.getLast)` and
`alpha (p.getLast)` lie at distinct vertices, the rest `r` is a noncrossing closed walk of the join
whose outer cycle follows its boundary. -/
theorem join_walk [DecidableEq Delta.toCombMap.Dart] (hr : r ≠ [])
    (hxy : ¬ Delta.toCombMap.sigma.SameCycle (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil))
      (Delta.toCombMap.alpha (p.getLast X.p_ne_nil)))
    (hM' : (VertexJoin.toCombMap Delta.toCombMap (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil))
      (Delta.toCombMap.alpha (p.getLast X.p_ne_nil))).IsPlanar) :
    ∃ hw : IsNoncrossingClosedWalk (VertexJoin.toCombMap Delta.toCombMap
        (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil))
        (Delta.toCombMap.alpha (p.getLast X.p_ne_nil))) r,
      (hw.outerCycle hM').FollowsBoundary := by
  obtain ⟨hw, hf⟩ := X.walk
  have ht := outerTurn_of_followsBoundary hw Delta.planar hf
  have hx : ¬ walkKeep Delta.toCombMap (p ++ r)
      (Delta.toCombMap.alpha (X.q.getLast X.q_ne_nil)) := by
    rw [walkKeep_alpha]
    exact X.join_not_walkKeep (List.getLast_mem X.q_ne_nil)
  have hσy : ¬ walkKeep Delta.toCombMap (p ++ r)
      (Delta.toCombMap.sigma (Delta.toCombMap.alpha (p.getLast X.p_ne_nil))) := by
    rw [X.join_sigma_alpha_p]
    exact X.join_not_walkKeep (List.head_mem X.q_ne_nil)
  exact ⟨isNoncrossingClosedWalk_vertexJoin_rest hw ht X.p_ne_nil hr hx X.join_sigma_alpha_q
      (Delta.toCombMap.alpha_involutive _) hσy X.cycle.chain.left_of_append hxy,
    followsBoundary_outerCycle _ hM'
      (outerTurn_vertexJoin_rest hw ht X.p_ne_nil X.join_sigma_alpha_q
        (Delta.toCombMap.alpha_involutive _))⟩

#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.NoncrossingStrip.join_not_walkKeep
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.NoncrossingStrip.join_planar
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.NoncrossingStrip.join_walk

end GroupApproximation.GGT.VanKampen.NoncrossingCollarStrip.NoncrossingStrip
