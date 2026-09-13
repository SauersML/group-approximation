import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkSides
import GroupApproximation.GGT.VanKampen.VertexJoinMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Noncrossing closed walks through the collar surgeries

The strip step of the geodesic collar construction moves a closed walk along two surgeries: an
edge insertion, which embeds the old map in the new one, and a vertex pinch
`VertexJoin.toCombMap M x y`, which splits the rotation at one vertex.  The simple closed walk
carrier survives both moves (`GeodesicCollar.isSimpleClosedWalk_map`,
`GeodesicCollar.isSimpleClosedWalk_pinch`).  This module shows that a noncrossing closed walk
survives them as well, together with the rotation condition under which the reversed walk
follows the boundary of the faces on the other side.

* `TurnsBack M w a b`: rotating around a vertex from the walk dart `b`, the first dart on an edge
  of the walk is the reversal of `a`.
* `OuterTurn M w`: every walk dart turns back to the walk dart before it, cyclically.
* `isNoncrossingClosedWalk_map`, `outerTurn_map`: transport along a restriction of maps, in
  particular along an edge insertion (`edgeInsertion_isRestriction`).
* `isNoncrossingClosedWalk_vertexJoin`, `outerTurn_vertexJoin`: a pinch separating the reversal
  of a walk dart from the rotation predecessor of a walk dart keeps both properties.

No vertex of the walk needs to be visited only once, and no inner boundary condition is used.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk

open Equiv SimpleClosedWalkSides

universe u v

/-- Rotating around a vertex from the walk dart `b`, the first dart on an edge of the walk `w` is
the reversal of `a`, so no edge of the walk leaves the vertex strictly between `b` and
`M.alpha a`. -/
def TurnsBack (M : CombMap.{u}) (w : List M.Dart) (a b : M.Dart) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (M.sigma ^ m) b = M.alpha a ∧
    ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) b)

/-- Every walk dart turns back to the walk dart before it, cyclically. -/
structure OuterTurn (M : CombMap.{u}) (w : List M.Dart) : Prop where
  chain : w.IsChain (TurnsBack M w)
  closes : ∀ hne : w ≠ [], TurnsBack M w (w.getLast hne) (w.head hne)

section Basic

variable {M : CombMap.{u}} {w : List M.Dart}

theorem vertexOf_eq_of_turnsBack {a b : M.Dart} (h : TurnsBack M w a b) :
    M.vertexOf (M.alpha a) = M.vertexOf b := by
  obtain ⟨m, _, hpm, _⟩ := h
  exact (M.vertexOf_eq_iff _ _).mpr
    (Equiv.Perm.SameCycle.symm ⟨(m : ℤ), by rw [zpow_natCast]; exact hpm⟩)

/-- Rotating from a dart on an edge of the walk, the first dart met on an edge of the walk. -/
theorem exists_first_keep {z : M.Dart} (hz : walkKeep M w z) :
    ∃ m : ℕ, 0 < m ∧ walkKeep M w ((M.sigma ^ m) z) ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) z) := by
  obtain ⟨m, hm, hret, havoid⟩ := (walkMap_isRestriction M w).sigma_firstReturn ⟨z, hz⟩
  exact ⟨m, hm, (congrArg (walkKeep M w) hret).mpr ((walkMap M w).sigma ⟨z, hz⟩).2,
    fun k hk0 hkm hkeep => havoid k hk0 hkm ⟨⟨_, hkeep⟩, rfl⟩⟩

/-- Rotating from the reversal of a walk dart, the first dart met on an edge of the walk is a
walk dart. -/
theorem exists_first_mem (hw : IsNoncrossingClosedWalk M w) {d : M.Dart} (hd : d ∈ w) :
    ∃ m : ℕ, 0 < m ∧ (M.sigma ^ m) (M.alpha d) ∈ w ∧
      ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) (M.alpha d)) := by
  obtain ⟨m, hm, hkeep, havoid⟩ := exists_first_keep (hw.alpha_keep hd)
  exact ⟨m, hm, hw.turn_mem d hd m hm hkeep havoid, havoid⟩

end Basic

/-- Iterating `p * swap x y` agrees with iterating `p` while the orbit avoids `x` and `y`. -/
theorem pow_mul_swap_apply {D : Type*} [DecidableEq D] (p : Perm D) (x y z : D) (n : ℕ)
    (h : ∀ k, k < n → (p ^ k) z ≠ x ∧ (p ^ k) z ≠ y) : ((p * swap x y) ^ n) z = (p ^ n) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih fun k hk => h k (by omega), Perm.mul_apply,
      swap_apply_of_ne_of_ne (h n (by omega)).1 (h n (by omega)).2, pow_succ', Perm.mul_apply]

section VertexJoin

variable {M : CombMap.{u}} [DecidableEq M.Dart] {w : List M.Dart} {x y : M.Dart}

/-- A walk dart turns back to its predecessor in the same way after the pinch. -/
theorem turnsBack_vertexJoin (hw : IsNoncrossingClosedWalk M w) (hx : M.alpha x ∈ w)
    (hy : M.sigma y ∈ w) {a b : M.Dart} (ha : a ∈ w) (hb : b ∈ w) (h : TurnsBack M w a b) :
    TurnsBack (VertexJoin.toCombMap M x y) w a b := by
  obtain ⟨m, hm, hpm, havoid⟩ := h
  have hpow : ∀ k, k ≤ m → ((VertexJoin.toCombMap M x y).sigma ^ k) b = (M.sigma ^ k) b := by
    intro k hkm
    refine pow_mul_swap_apply M.sigma x y b k fun j hj => ⟨fun hjx => ?_, fun hjy => ?_⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [pow_zero, Perm.one_apply] at hjx
        exact hw.alpha_not_mem _ hx (by rw [M.alpha_involutive x, ← hjx]; exact hb)
      · exact havoid j hj0 (by omega) (Or.inr (by rw [hjx]; exact hx))
    · have hsucc : (M.sigma ^ (j + 1)) b = M.sigma y := by
        rw [pow_succ', Perm.mul_apply, hjy]
      rcases Nat.lt_or_ge (j + 1) m with hlt | hge
      · exact havoid (j + 1) (Nat.succ_pos j) hlt (Or.inl (by rw [hsucc]; exact hy))
      · rw [show j + 1 = m by omega, hpm] at hsucc
        exact hw.alpha_not_mem a ha (by rw [hsucc]; exact hy)
  refine ⟨m, hm, by rw [hpow m le_rfl]; exact hpm, fun k hk0 hkm hkeep => havoid k hk0 hkm ?_⟩
  rw [← hpow k hkm.le]
  exact hkeep

theorem outerTurn_vertexJoin (hw : IsNoncrossingClosedWalk M w) (ht : OuterTurn M w)
    (hx : M.alpha x ∈ w) (hy : M.sigma y ∈ w) : OuterTurn (VertexJoin.toCombMap M x y) w where
  chain := ht.chain.imp_of_mem_imp fun _ _ ha hb h => turnsBack_vertexJoin hw hx hy ha hb h
  closes hne := turnsBack_vertexJoin hw hx hy (List.getLast_mem hne) (List.head_mem hne)
    (ht.closes hne)

/-- After the pinch, rotating from the reversal of a walk dart still first meets a walk dart. -/
theorem exists_first_mem_vertexJoin (hw : IsNoncrossingClosedWalk M w) (hx : M.alpha x ∈ w)
    (hy : M.sigma y ∈ w) {d : M.Dart} (hd : d ∈ w) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ((VertexJoin.toCombMap M x y).sigma ^ m₀) (M.alpha d) ∈ w ∧
      ∀ k, 0 < k → k < m₀ →
        ¬ walkKeep M w (((VertexJoin.toCombMap M x y).sigma ^ k) (M.alpha d)) := by
  by_cases hdx : M.alpha d = x
  · refine ⟨1, Nat.one_pos, ?_, fun k hk0 hk1 =>
      absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩
    rw [pow_one]
    show M.sigma (swap x y (M.alpha d)) ∈ w
    rw [hdx, swap_apply_left]
    exact hy
  obtain ⟨m, hm, hmem, havoid⟩ := exists_first_mem hw hd
  have hnx : ∀ k, k < m → (M.sigma ^ k) (M.alpha d) ≠ x := by
    intro k hkm hkx
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, Perm.one_apply] at hkx
      exact hdx hkx
    · exact havoid k hk0 hkm (Or.inr (by rw [hkx]; exact hx))
  by_cases hyj : ∃ j, j < m ∧ (M.sigma ^ j) (M.alpha d) = y
  swap
  · have hpow : ∀ k, k ≤ m → ((VertexJoin.toCombMap M x y).sigma ^ k) (M.alpha d) =
        (M.sigma ^ k) (M.alpha d) := fun k hk =>
      pow_mul_swap_apply M.sigma x y (M.alpha d) k fun j hj =>
        ⟨hnx j (by omega), fun hjy => hyj ⟨j, by omega, hjy⟩⟩
    refine ⟨m, hm, by rw [hpow m le_rfl]; exact hmem, fun k hk0 hkm hkeep => havoid k hk0 hkm ?_⟩
    rw [← hpow k hkm.le]
    exact hkeep
  obtain ⟨j, hjm, hjy⟩ := hyj
  have hjm' : j + 1 = m := by
    rcases Nat.lt_or_ge (j + 1) m with hlt | hge
    · exact (havoid (j + 1) (Nat.succ_pos j) hlt
        (Or.inl (by rw [pow_succ', Perm.mul_apply, hjy]; exact hy))).elim
    · omega
  subst hjm'
  obtain ⟨n, hn, hnmem, hnavoid⟩ := exists_first_mem hw hx
  rw [M.alpha_involutive x] at hnmem hnavoid
  have hyx : ∀ i, 0 < i → i < n → (M.sigma ^ i) x ≠ y := by
    intro i hi0 hin hixy
    rcases Nat.lt_or_ge j i with hji | hij
    · obtain ⟨t, rfl⟩ : ∃ t, i = j + t := ⟨i - j, by omega⟩
      rw [pow_add, Perm.mul_apply] at hixy
      have hxt : (M.sigma ^ t) x = M.alpha d := (M.sigma ^ j).injective (hixy.trans hjy.symm)
      exact hnavoid t (by omega) (by omega)
        (Or.inr (by rw [hxt, M.alpha_involutive d]; exact hd))
    · obtain ⟨t, rfl⟩ : ∃ t, j = i + t := ⟨j - i, by omega⟩
      rw [pow_add, Perm.mul_apply] at hjy
      exact hnx t (by omega) ((M.sigma ^ i).injective (hjy.trans hixy.symm))
  have hpre : ∀ k, k ≤ j → ((VertexJoin.toCombMap M x y).sigma ^ k) (M.alpha d) =
      (M.sigma ^ k) (M.alpha d) := by
    intro k hkj
    refine pow_mul_swap_apply M.sigma x y (M.alpha d) k fun i hi =>
      ⟨hnx i (by omega), fun hiy => ?_⟩
    exact havoid (i + 1) (Nat.succ_pos i) (by omega)
      (Or.inl (by rw [pow_succ', Perm.mul_apply, hiy]; exact hy))
  have hstep : ((VertexJoin.toCombMap M x y).sigma ^ (j + 1)) (M.alpha d) = M.sigma x := by
    rw [pow_succ', Perm.mul_apply, hpre j le_rfl]
    show M.sigma (swap x y ((M.sigma ^ j) (M.alpha d))) = M.sigma x
    rw [hjy, swap_apply_right]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hpost : ∀ l, l ≤ n' → ((VertexJoin.toCombMap M x y).sigma ^ l) (M.sigma x) =
      (M.sigma ^ (l + 1)) x := by
    intro l hln
    rw [pow_succ, Perm.mul_apply]
    refine pow_mul_swap_apply M.sigma x y (M.sigma x) l fun i hi =>
      ⟨fun hix => ?_, fun hiy => ?_⟩
    · rw [← Perm.mul_apply, ← pow_succ] at hix
      exact hnavoid (i + 1) (Nat.succ_pos i) (by omega) (Or.inr (by rw [hix]; exact hx))
    · rw [← Perm.mul_apply, ← pow_succ] at hiy
      exact hyx (i + 1) (Nat.succ_pos i) (by omega) hiy
  have hcomp : ∀ l, l ≤ n' →
      ((VertexJoin.toCombMap M x y).sigma ^ (l + (j + 1))) (M.alpha d) = (M.sigma ^ (l + 1)) x := by
    intro l hln
    rw [pow_add, Perm.mul_apply, hstep, hpost l hln]
  refine ⟨n' + (j + 1), by omega, by rw [hcomp n' le_rfl]; exact hnmem,
    fun k hk0 hkm hkeep => ?_⟩
  rcases Nat.lt_or_ge j k with hjk | hkj
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + (j + 1) := ⟨k - (j + 1), by omega⟩
    rw [hcomp l (by omega)] at hkeep
    exact hnavoid (l + 1) (Nat.succ_pos l) (by omega) hkeep
  · rw [hpre k hkj] at hkeep
    exact havoid k hk0 (by omega) hkeep

/-- **A pinch keeps a noncrossing closed walk that turns back.**  Separating the reversal `x` of
a walk dart from the rotation predecessor `y` of a walk dart keeps the walk noncrossing. -/
theorem isNoncrossingClosedWalk_vertexJoin (hw : IsNoncrossingClosedWalk M w)
    (ht : OuterTurn M w) (hx : M.alpha x ∈ w) (hy : M.sigma y ∈ w) :
    IsNoncrossingClosedWalk (VertexJoin.toCombMap M x y) w where
  ne_nil := hw.ne_nil
  nodup := hw.nodup
  chain := (outerTurn_vertexJoin hw ht hx hy).chain.imp_of_mem_imp fun _ _ _ _ h =>
    vertexOf_eq_of_turnsBack h
  closes := vertexOf_eq_of_turnsBack ((outerTurn_vertexJoin hw ht hx hy).closes hw.ne_nil)
  alpha_not_mem := hw.alpha_not_mem
  turn_mem d hd := by
    obtain ⟨m₀, hm₀, hmem₀, havoid₀⟩ := exists_first_mem_vertexJoin hw hx hy hd
    exact NoncrossingClosedWalkSides.turn_mem_of_first hm₀ hmem₀ havoid₀

end VertexJoin

section Restriction

variable {M : CombMap.{u}} {N : CombMap.{v}} {ι : N.Dart ↪ M.Dart} {w : List N.Dart}

theorem exists_of_walkKeep_map (hι : M.IsRestriction N ι) {z : M.Dart}
    (hz : walkKeep M (w.map ι) z) : ∃ c, ι c = z ∧ walkKeep N w c := by
  rcases hz with hz | hz
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact ⟨c, rfl, Or.inl hc⟩
  · obtain ⟨c, hc, hcz⟩ := List.mem_map.mp hz
    refine ⟨N.alpha c, ?_, Or.inr ?_⟩
    · rw [hι.alpha_map c, hcz, M.alpha_involutive z]
    · rw [N.alpha_involutive c]
      exact hc

/-- A rotation run avoiding the walk edges in a restriction is a run in the ambient map. -/
theorem turn_map (hι : M.IsRestriction N ι) {z t : N.Dart} {m : ℕ} (hm : 0 < m)
    (hmt : (N.sigma ^ m) z = t)
    (havoid : ∀ k, 0 < k → k < m → ¬ walkKeep N w ((N.sigma ^ k) z)) :
    ∃ m' : ℕ, 0 < m' ∧ (M.sigma ^ m') (ι z) = ι t ∧
      ∀ k, 0 < k → k < m' → ¬ walkKeep M (w.map ι) ((M.sigma ^ k) (ι z)) := by
  obtain ⟨m', hm', hret, htrace⟩ :=
    PermFirstReturn.iterate M.sigma N.sigma ι hι.sigma_firstReturn m z
  refine ⟨m', by omega, hret.trans (congrArg ι hmt), fun k hk0 hkm hkeep => ?_⟩
  obtain ⟨c, hc, hkc⟩ := exists_of_walkKeep_map hι hkeep
  obtain ⟨j, hjm, hj0, hj⟩ := htrace k hkm ⟨c, hc⟩
  refine havoid j (hj0 hk0) hjm ?_
  rw [← ι.injective (hc.trans hj)]
  exact hkc

theorem turnsBack_map (hι : M.IsRestriction N ι) {a b : N.Dart} (h : TurnsBack N w a b) :
    TurnsBack M (w.map ι) (ι a) (ι b) := by
  obtain ⟨m, hm, hpm, havoid⟩ := h
  obtain ⟨m', hm', hret, havoid'⟩ := turn_map hι hm hpm havoid
  exact ⟨m', hm', hret.trans (hι.alpha_map a), havoid'⟩

theorem outerTurn_map (hι : M.IsRestriction N ι) (ht : OuterTurn N w) :
    OuterTurn M (w.map ι) where
  chain := (List.isChain_map ι).mpr
    (ht.chain.imp_of_mem_imp fun _ _ _ _ h => turnsBack_map hι h)
  closes hne := by
    simp only [List.getLast_map, List.head_map]
    exact turnsBack_map hι (ht.closes (mt List.map_eq_nil_iff.mpr hne))

/-- **A noncrossing closed walk transports along a restriction of maps.** -/
theorem isNoncrossingClosedWalk_map (hι : M.IsRestriction N ι)
    (hw : IsNoncrossingClosedWalk N w) : IsNoncrossingClosedWalk M (w.map ι) where
  ne_nil := mt List.map_eq_nil_iff.mp hw.ne_nil
  nodup := hw.nodup.map ι.injective
  chain := (List.isChain_map ι).mpr <| hw.chain.imp_of_mem_imp fun d e _ _ h =>
    show M.vertexOf (M.alpha (ι d)) = M.vertexOf (ι e) by
      rw [← hι.alpha_map d, ← hι.vertexOf_eq_iff]
      exact h
  closes := by
    simp only [List.getLast_map, List.head_map]
    rw [← hι.alpha_map, ← hι.vertexOf_eq_iff]
    exact hw.closes
  alpha_not_mem d' hd' := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    rw [← hι.alpha_map d, List.mem_map_of_injective ι.injective]
    exact hw.alpha_not_mem d hd
  turn_mem d' hd' := by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    obtain ⟨m₁, hm₁, hmem₁, havoid₁⟩ := exists_first_mem hw hd
    obtain ⟨m', hm', hret, havoid'⟩ := turn_map hι hm₁ rfl havoid₁
    rw [hι.alpha_map d] at hret havoid'
    exact NoncrossingClosedWalkSides.turn_mem_of_first hm'
      (by rw [hret]; exact List.mem_map_of_mem hmem₁) havoid'

end Restriction

/-- Inserting a point before `a` in a permutation: the old permutation is its first return. -/
theorem insertBefore_isFirstReturn {D : Type u} (p : Perm D) (a : D) :
    PermFirstReturn.IsFirstReturn (PermOrbitInsert.insertBefore p a) p
      Function.Embedding.some := by
  classical
  intro b
  by_cases hb : p b = a
  · refine ⟨2, by omega, ?_, fun k hk0 hk2 => ?_⟩
    · show (PermOrbitInsert.insertBefore p a ^ 2) (some b) = some (p b)
      rw [pow_two, Perm.mul_apply, PermOrbitInsert.insertBefore_some, if_pos hb,
        PermOrbitInsert.insertBefore_none, hb]
    · obtain rfl : k = 1 := by omega
      rintro ⟨c, hc⟩
      have hc' : some c = PermOrbitInsert.insertBefore p a (some b) := by
        rw [pow_one] at hc
        exact hc
      rw [PermOrbitInsert.insertBefore_some, if_pos hb] at hc'
      exact Option.some_ne_none c hc'
  · refine ⟨1, Nat.one_pos, ?_, fun k hk0 hk1 =>
      absurd hk0 (Nat.not_lt.mpr (Nat.le_of_lt_succ hk1))⟩
    show (PermOrbitInsert.insertBefore p a ^ 1) (some b) = some (p b)
    rw [pow_one, PermOrbitInsert.insertBefore_some, if_neg hb]

/-- **An edge insertion is a restriction** onto the old darts. -/
theorem edgeInsertion_isRestriction (M : CombMap.{u}) (a b : M.Dart) :
    (EdgeInsertion.toCombMap M a b).IsRestriction M
      (Function.Embedding.trans Function.Embedding.some Function.Embedding.some) where
  alpha_map _ := rfl
  sigma_firstReturn := PermFirstReturn.trans
    (PermOrbitInsert.insertBefore (PermOrbitInsert.insertBefore M.sigma a) (some b))
    (PermOrbitInsert.insertBefore M.sigma a) M.sigma Function.Embedding.some
    Function.Embedding.some (insertBefore_isFirstReturn _ _) (insertBefore_isFirstReturn _ _)

theorem isNoncrossingClosedWalk_edgeInsertion {M : CombMap.{u}} {w : List M.Dart} (a b : M.Dart)
    (hw : IsNoncrossingClosedWalk M w) :
    IsNoncrossingClosedWalk (EdgeInsertion.toCombMap M a b) (w.map (EdgeInsertion.embed M)) :=
  isNoncrossingClosedWalk_map (edgeInsertion_isRestriction M a b) hw

theorem outerTurn_edgeInsertion {M : CombMap.{u}} {w : List M.Dart} (a b : M.Dart)
    (ht : OuterTurn M w) :
    OuterTurn (EdgeInsertion.toCombMap M a b) (w.map (EdgeInsertion.embed M)) :=
  outerTurn_map (edgeInsertion_isRestriction M a b) ht

#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.vertexOf_eq_of_turnsBack
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.exists_first_mem
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.pow_mul_swap_apply
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.outerTurn_vertexJoin
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.isNoncrossingClosedWalk_vertexJoin
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.outerTurn_map
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.isNoncrossingClosedWalk_map
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.edgeInsertion_isRestriction
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.isNoncrossingClosedWalk_edgeInsertion
#audit_axioms GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk.outerTurn_edgeInsertion

end GroupApproximation.GGT.VanKampen.NoncrossingCollarWalk
