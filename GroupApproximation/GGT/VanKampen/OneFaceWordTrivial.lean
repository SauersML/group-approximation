import GroupApproximation.GGT.VanKampen.SpikeDeletion
import GroupApproximation.GGT.VanKampen.CyclicFaceBoundary
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# The boundary word of a one-face planar map is freely trivial

A planar combinatorial map with a single face is a tree.  If its darts carry
relative letters with `label (alpha d) = inv (label d)`, the word read around
that face has value one:
`listVal_faceBoundary_eq_one_of_faceCount_eq_one`.

The proof is the classical spike induction.  A one-face planar map has a
vertex of degree one (`CombMap.exists_sigma_eq_self_of_planar_faceCount_eq_one`),
its two darts are consecutive around the face with inverse labels, and deleting
the edge leaves a planar map with one face and two fewer darts
(`GGT/VanKampen/SpikeDeletion.lean`).  The face traversal is handled through
`orbitWalk`, the literal list of the first `n` points of an orbit, so a
rotation of the chosen starting dart is a `List.rotate` and only conjugates the
value.

This is the tree case of the easy van Kampen lemma for planar relator-only
maps, the input needed to recompute the ordered relator cells of a folded disc.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv HullSC

universe u w v

/-! ## Walks along a permutation -/

section Walk

variable {D : Type u} (p : Perm D)

/-- The first `n` points of the orbit of `x`, in order. -/
def orbitWalk : D → ℕ → List D
  | _, 0 => []
  | x, n + 1 => x :: orbitWalk (p x) n

theorem orbitWalk_zero (x : D) : orbitWalk p x 0 = [] := rfl

theorem orbitWalk_succ (x : D) (n : ℕ) :
    orbitWalk p x (n + 1) = x :: orbitWalk p (p x) n := rfl

theorem length_orbitWalk (x : D) (n : ℕ) : (orbitWalk p x n).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [orbitWalk_succ, List.length_cons, ih]

/-- Appending the next point at the end. -/
theorem orbitWalk_succ' (x : D) (n : ℕ) :
    orbitWalk p x (n + 1) = orbitWalk p x n ++ [(p ^ n) x] := by
  induction n generalizing x with
  | zero => simp [orbitWalk_succ, orbitWalk_zero]
  | succ n ih =>
      rw [orbitWalk_succ p x (n + 1), ih (p x), orbitWalk_succ p x n, List.cons_append,
        pow_succ, Perm.mul_apply]

/-- Consecutive points of a walk follow the permutation. -/
theorem isChain_orbitWalk (x : D) (n : ℕ) :
    (orbitWalk p x n).IsChain (fun d e => p d = e) := by
  induction n generalizing x with
  | zero => exact List.isChain_nil
  | succ n ih =>
      cases n with
      | zero => exact List.isChain_singleton _
      | succ m =>
          rw [orbitWalk_succ p x (m + 1), orbitWalk_succ p (p x) m, List.isChain_cons_cons]
          refine ⟨rfl, ?_⟩
          have h := ih (p x)
          rwa [orbitWalk_succ p (p x) m] at h

theorem mem_orbitWalk {x y : D} {n : ℕ} :
    y ∈ orbitWalk p x n ↔ ∃ j < n, (p ^ j) x = y := by
  induction n generalizing x with
  | zero => simp [orbitWalk_zero]
  | succ n ih =>
      rw [orbitWalk_succ, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨j, hj, h⟩)
        · exact ⟨0, Nat.succ_pos n, by simp [h]⟩
        · exact ⟨j + 1, by omega, by rw [← h, pow_succ, Perm.mul_apply]⟩
      · rintro ⟨j, hj, h⟩
        cases j with
        | zero => exact Or.inl (by rw [← h]; simp)
        | succ j => exact Or.inr ⟨j, by omega, by rw [← h, pow_succ, Perm.mul_apply]⟩

/-- A list following a permutation is the walk from its head. -/
theorem eq_orbitWalk_of_isChain :
    ∀ (l : List D) (x : D), l.IsChain (fun d e => p d = e) → l.head? = some x →
      l = orbitWalk p x l.length
  | [], _, _, h => by simp at h
  | [y], x, _, h => by
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      rfl
  | y :: z :: t, x, hc, h => by
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      rw [List.isChain_cons_cons] at hc
      have hyz : p y = z := hc.1
      have ih := eq_orbitWalk_of_isChain (z :: t) z hc.2 rfl
      change y :: z :: t = y :: orbitWalk p (p y) (z :: t).length
      rw [hyz, ← ih]

theorem getLast_orbitWalk (x : D) (n : ℕ) (hne : orbitWalk p x (n + 1) ≠ []) :
    (orbitWalk p x (n + 1)).getLast hne = (p ^ n) x := by
  rw [List.getLast_congr hne (by simp) (orbitWalk_succ' p x n), List.getLast_append_singleton]

/-- Starting one step later rotates a periodic walk by one. -/
theorem orbitWalk_apply_eq_rotate_one (x : D) (n : ℕ) (hx : (p ^ n) x = x) :
    orbitWalk p (p x) n = (orbitWalk p x n).rotate 1 := by
  cases n with
  | zero => simp [orbitWalk_zero]
  | succ n =>
      have hpx : (p ^ n) (p x) = x := by
        rw [← Perm.mul_apply, ← pow_succ, hx]
      rw [orbitWalk_succ' p (p x) n, orbitWalk_succ p x n, hpx]
      simp only [List.rotate_cons_succ, List.rotate_zero]

/-- Starting `k` steps later rotates a periodic walk by `k`. -/
theorem orbitWalk_pow_eq_rotate (x : D) (n : ℕ) (hx : (p ^ n) x = x) :
    ∀ k : ℕ, orbitWalk p ((p ^ k) x) n = (orbitWalk p x n).rotate k
  | 0 => by rw [pow_zero, Perm.one_apply, List.rotate_zero]
  | k + 1 => by
      have hk : (p ^ n) ((p ^ k) x) = (p ^ k) x := by
        rw [← Perm.mul_apply, ← pow_add, add_comm, pow_add, Perm.mul_apply, hx]
      rw [pow_succ', Perm.mul_apply, orbitWalk_apply_eq_rotate_one p _ n hk,
        orbitWalk_pow_eq_rotate x n hx k, List.rotate_rotate]

/-- The points of a duplicate-free walk are pairwise distinct. -/
theorem ne_of_nodup_orbitWalk {x : D} {n : ℕ} (hnd : (orbitWalk p x n).Nodup) :
    ∀ {i j : ℕ}, i < j → j < n → (p ^ i) x ≠ (p ^ j) x := by
  induction n generalizing x with
  | zero => intro i j _ hj; omega
  | succ n ih =>
      intro i j hij hj
      rw [orbitWalk_succ, List.nodup_cons] at hnd
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      cases i with
      | zero =>
          intro h
          apply hnd.1
          rw [mem_orbitWalk]
          refine ⟨j', by omega, ?_⟩
          rw [← Perm.mul_apply, ← pow_succ, ← h, pow_zero, Perm.one_apply]
      | succ i =>
          have h := ih hnd.2 (i := i) (j := j') (by omega) (by omega)
          rwa [← Perm.mul_apply, ← Perm.mul_apply, ← pow_succ, ← pow_succ] at h

end Walk

/-! ## Face rotation after deleting a spike -/

namespace EdgeDeletion

variable (M : CombMap.{u}) [DecidableEq M.Dart] (a : M.Dart)

/-- **Face rotation after deleting a spike.**  A surviving dart that led into the
deleted edge now jumps to the dart that followed the tip. -/
theorem value_facePerm_of_fixed (ha : M.sigma a = a) (d : Dart M a) :
    value M a ((toCombMap M a).facePerm d) =
      if M.facePerm (value M a d) = M.alpha a then M.facePerm a
      else M.facePerm (value M a d) := by
  have hv := value_sigma_of_fixed M a ha (alpha M a d)
  have hα := alpha_val M a d
  change value M a ((toCombMap M a).sigma (alpha M a d)) = _
  rw [hv, hα]
  rfl

end EdgeDeletion

/-! ## The tree lemma -/

/-- **The boundary word of a one-face planar map is freely trivial.** -/
theorem listVal_faceBoundary_eq_one_of_faceCount_eq_one {G : Type w} [Group G]
    {Lambda : Type v} :
    ∀ (n : ℕ) (M : CombMap.{u}), M.edgeCount = n → M.IsPlanar → M.faceCount = 1 →
      ∀ (label : M.Dart → GGT.RelLetter G Lambda),
        (∀ d, label (M.alpha d) = RelWord.inv (label d)) →
        ∀ (f : M.Face) (B : FaceBoundary M f),
          GGT.RelLetter.listVal (B.darts.map label) = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M hn hM hF label hlabel f B
  classical
  have hsub : Subsingleton M.Face := (Nat.card_eq_one_iff_unique.mp hF).1
  have hall : ∀ x : M.Dart, x ∈ B.darts :=
    fun x => (B.mem_iff x).mpr (Subsingleton.elim _ _)
  obtain ⟨m, hm⟩ : ∃ m, B.darts.length = m + 1 :=
    ⟨B.darts.length - 1, by
      have := List.length_pos_iff_ne_nil.mpr B.nonempty
      omega⟩
  have hwalk : B.darts = orbitWalk M.facePerm (B.darts.head B.nonempty) (m + 1) := by
    rw [← hm]
    exact eq_orbitWalk_of_isChain M.facePerm B.darts _ B.chain
      (List.head?_eq_some_head B.nonempty)
  have hperiod : (M.facePerm ^ (m + 1)) (B.darts.head B.nonempty) =
      B.darts.head B.nonempty := by
    have hc := B.closes
    rw [List.getLast_congr B.nonempty (by simp [orbitWalk_succ]) hwalk,
      getLast_orbitWalk] at hc
    rw [pow_succ', Perm.mul_apply, hc]
  obtain ⟨d, hd⟩ := M.exists_sigma_eq_self_of_planar_faceCount_eq_one hM hF
  have hαd : M.facePerm (M.alpha d) = d := by
    show M.sigma (M.alpha (M.alpha d)) = d
    rw [M.alpha_involutive, hd]
  obtain ⟨j, hj, hjd⟩ := (mem_orbitWalk M.facePerm).mp (hwalk ▸ hall d)
  have hyp : M.facePerm d = (M.facePerm ^ (j + 1)) (B.darts.head B.nonempty) := by
    rw [pow_succ', Perm.mul_apply, hjd]
  have hperiody : (M.facePerm ^ (m + 1)) (M.facePerm d) = M.facePerm d := by
    rw [hyp, ← Perm.mul_apply, ← pow_add, add_comm, pow_add, Perm.mul_apply, hperiod]
  have hrot : orbitWalk M.facePerm (M.facePerm d) (m + 1) =
      (orbitWalk M.facePerm (B.darts.head B.nonempty) (m + 1)).rotate (j + 1) := by
    rw [hyp]
    exact orbitWalk_pow_eq_rotate M.facePerm _ (m + 1) hperiod (j + 1)
  have hnd : (orbitWalk M.facePerm (M.facePerm d) (m + 1)).Nodup := by
    rw [hrot, List.nodup_rotate, ← hwalk]
    exact B.nodup
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := by
    rcases m with _ | k
    · exfalso
      obtain ⟨j', hj', hj'd⟩ := (mem_orbitWalk M.facePerm).mp (hwalk ▸ hall (M.alpha d))
      have hj0 : j = 0 := by omega
      have hj'0 : j' = 0 := by omega
      subst hj0 hj'0
      exact M.alpha_fixedPointFree d (hj'd.symm.trans hjd)
    · exact ⟨k, rfl⟩
  subst hk
  have hlastd : (M.facePerm ^ (k + 1)) (M.facePerm d) = d := by
    apply M.facePerm.injective
    rw [← Perm.mul_apply, ← pow_succ', hperiody]
  have hlastαd : (M.facePerm ^ k) (M.facePerm d) = M.alpha d := by
    apply M.facePerm.injective
    rw [← Perm.mul_apply, ← pow_succ', hlastd, hαd]
  have hsplit : orbitWalk M.facePerm (M.facePerm d) (k + 1 + 1) =
      orbitWalk M.facePerm (M.facePerm d) k ++ [M.alpha d, d] := by
    rw [orbitWalk_succ' M.facePerm _ (k + 1), orbitWalk_succ' M.facePerm _ k, hlastd,
      hlastαd, List.append_assoc]
    rfl
  have hval_split :
      GGT.RelLetter.listVal ((orbitWalk M.facePerm (M.facePerm d) (k + 1 + 1)).map label) =
        GGT.RelLetter.listVal ((orbitWalk M.facePerm (M.facePerm d) k).map label) := by
    rw [hsplit, List.map_append, RelWord.listVal_append]
    simp only [List.map_cons, List.map_nil, RelWord.listVal_cons, GGT.RelLetter.listVal_nil,
      mul_one, hlabel, RelWord.val_inv, inv_mul_cancel]
  have hB : GGT.RelLetter.listVal (B.darts.map label) = 1 ↔
      GGT.RelLetter.listVal
        ((orbitWalk M.facePerm (M.facePerm d) (k + 1 + 1)).map label) = 1 := by
    rw [hrot, List.map_rotate]
    conv_lhs => rw [hwalk]
    have hlen : j + 1 ≤
        ((orbitWalk M.facePerm (B.darts.head B.nonempty) (k + 1 + 1)).map label).length := by
      rw [List.length_map, length_orbitWalk]
      omega
    rw [RelWord.listVal_rotate _ hlen]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      have h' := congrArg (fun z => GGT.RelLetter.listVal
          (((orbitWalk M.facePerm (B.darts.head B.nonempty) (k + 1 + 1)).map label).take
            (j + 1)) * z *
          (GGT.RelLetter.listVal
            (((orbitWalk M.facePerm (B.darts.head B.nonempty) (k + 1 + 1)).map label).take
              (j + 1)))⁻¹) h
      simpa [mul_assoc] using h'
  rw [hB, hval_split]
  rcases k with _ | k
  · rfl
  have hy_ne_d : M.facePerm d ≠ d := by
    intro h
    exact ne_of_nodup_orbitWalk M.facePerm hnd (i := 0) (j := k + 1 + 1) (by omega) (by omega)
      (by rw [pow_zero, Perm.one_apply, hlastd]; exact h)
  have hy_ne_αd : M.facePerm d ≠ M.alpha d := by
    intro h
    exact ne_of_nodup_orbitWalk M.facePerm hnd (i := 0) (j := k + 1) (by omega) (by omega)
      (by rw [pow_zero, Perm.one_apply, hlastαd]; exact h)
  let d₀ : EdgeDeletion.Dart M d :=
    ⟨⟨M.facePerm d, hy_ne_d⟩, fun h => hy_ne_αd (congrArg Subtype.val h)⟩
  have hNplanar : (EdgeDeletion.toCombMap M d).IsPlanar :=
    EdgeDeletion.planar_of_sigma_fixed M d hM hd d₀
  have hNface : (EdgeDeletion.toCombMap M d).faceCount = 1 :=
    EdgeDeletion.faceCount_eq_one_of_sigma_fixed M d hM hF hd d₀
  have hNedge : (EdgeDeletion.toCombMap M d).edgeCount + 1 = n := by
    rw [← hn]
    exact EdgeDeletion.edgeCount_add_one M d
  let labelN : (EdgeDeletion.toCombMap M d).Dart → GGT.RelLetter G Lambda :=
    fun e => label (EdgeDeletion.value M d e)
  have hlabelN : ∀ e, labelN ((EdgeDeletion.toCombMap M d).alpha e) = RelWord.inv (labelN e) := by
    intro e
    show label (EdgeDeletion.value M d (EdgeDeletion.alpha M d e)) = _
    rw [EdgeDeletion.alpha_val, hlabel]
  have hstep : ∀ i, i < k + 1 →
      EdgeDeletion.value M d (((EdgeDeletion.toCombMap M d).facePerm ^ i) d₀) =
        (M.facePerm ^ i) (M.facePerm d) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih' =>
        intro hi
        rw [pow_succ', Perm.mul_apply, EdgeDeletion.value_facePerm_of_fixed M d hd,
          ih' (by omega)]
        have hne : (M.facePerm ^ (i + 1)) (M.facePerm d) ≠ M.alpha d := by
          rw [← hlastαd]
          exact ne_of_nodup_orbitWalk M.facePerm hnd (i := i + 1) (j := k + 1)
            (by omega) (by omega)
        have hshift : M.facePerm ((M.facePerm ^ i) (M.facePerm d)) =
            (M.facePerm ^ (i + 1)) (M.facePerm d) := by
          rw [pow_succ', Perm.mul_apply]
        rw [hshift, if_neg hne]
  have hmap : ∀ i, i ≤ k + 1 →
      (orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ i).map (EdgeDeletion.value M d) =
        orbitWalk M.facePerm (M.facePerm d) i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih' =>
        intro hi
        rw [orbitWalk_succ', orbitWalk_succ']
        erw [List.map_append, ih' (by omega), List.map_cons, List.map_nil, hstep i (by omega)]
  have hWne : orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1) ≠ [] := by
    simp [orbitWalk_succ]
  have hWnd : (orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)).Nodup := by
    have h1 : (orbitWalk M.facePerm (M.facePerm d) (k + 1)).Nodup := by
      rw [hsplit] at hnd
      exact hnd.of_append_left
    rw [← hmap (k + 1) le_rfl] at h1
    exact h1.of_map _
  have hcond : M.facePerm ((M.facePerm ^ k) (M.facePerm d)) = M.alpha d := by
    rw [← hlastαd, pow_succ', Perm.mul_apply]
  have hWclose : (EdgeDeletion.toCombMap M d).facePerm
      ((orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)).getLast hWne) =
        (orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)).head hWne := by
    rw [getLast_orbitWalk]
    apply Subtype.ext
    apply Subtype.ext
    change EdgeDeletion.value M d ((EdgeDeletion.toCombMap M d).facePerm
      (((EdgeDeletion.toCombMap M d).facePerm ^ k) d₀)) = M.facePerm d
    rw [EdgeDeletion.value_facePerm_of_fixed M d hd, hstep k (by omega), if_pos hcond]
  have hIH := ih (EdgeDeletion.toCombMap M d).edgeCount (by omega)
    (EdgeDeletion.toCombMap M d) rfl hNplanar hNface labelN hlabelN _
    (FaceBoundary.ofCyclicList (EdgeDeletion.toCombMap M d)
      (orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)) hWne hWnd
      (isChain_orbitWalk _ d₀ (k + 1)) hWclose)
  have hlist : (orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)).map labelN =
      (orbitWalk M.facePerm (M.facePerm d) (k + 1)).map label := by
    rw [← hmap (k + 1) le_rfl, List.map_map]
    rfl
  change GGT.RelLetter.listVal
    ((orbitWalk (EdgeDeletion.toCombMap M d).facePerm d₀ (k + 1)).map labelN) = 1 at hIH
  rw [hlist] at hIH
  exact hIH

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.orbitWalk_succ'
#audit_axioms GroupApproximation.GGT.VanKampen.eq_orbitWalk_of_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.orbitWalk_pow_eq_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.ne_of_nodup_orbitWalk
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeDeletion.value_facePerm_of_fixed
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_faceBoundary_eq_one_of_faceCount_eq_one
