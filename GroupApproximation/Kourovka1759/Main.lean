import GroupApproximation.Kourovka1759.Base

/-!
# Kourovka Notebook Problem 17.59

`CT(ℤ)` is exactly the group of residue-class-wise affine permutations of `ℤ` that preserve
the sign of every integer.

A piecewise-canonical `g` maps the classes mod `L` canonically onto boxes `B j`. Refine the
class `j` and the box `B j` by the same split, of size `k j = N / (B j).m`: the refined source
is a two-level tree, and the refined target is the partition of `ℤ` by the classes mod `N`.
Both have types and the same number of pieces, so some element of `CT(ℤ)` maps one onto the
other canonically; then `g` differs from it by a reordering of disjoint boxes, which lies in
`CT(ℤ)` too.
-/

namespace GroupApproximation.Kourovka1759

open Equiv Box STree

/-- **Free bijection.** If `g` maps the boxes of `c` canonically onto those of a partition `d`,
and some element of `CT(ℤ)` does too (in some order), then `g ∈ CT(ℤ)`. -/
theorem mem_ct_of_canon {g : Perm ℤ} {c d : List Box} (hg : List.Forall₂ (CanonOn g) c d)
    (hd : d.Pairwise Box.Disj) (hcov : ∀ n, ∃ B ∈ d, B.Mem n) (h : MEq c d) :
    g ∈ classTranspositionGroup := by
  obtain ⟨f, hf, d', hp, hfd⟩ := MEq.to_equi h
  have hσ := forall₂_canon_comp (forall₂_canon_inv hfd) hg
  obtain ⟨τ, hτ, hτf, -⟩ := sym_perm hp ((hp.pairwise_iff (fun h => h.symm)).2 hd)
  have hid := forall₂_canon_comp (forall₂_canon_inv hτf) hσ
  have heq : g * f⁻¹ * τ⁻¹ = 1 := by
    refine Equiv.ext fun n => ?_
    obtain ⟨B, hB, hn⟩ := hcov n
    exact ((forall₂_diag hid B hB).apply hn).trans (B.eq_of_mem hn)
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at heq
  rw [heq]
  exact mul_mem hτ hf

theorem classOf_child {L : ℕ} (hL : 0 < L) (j : Fin L) : classOf L hL (child L j).r = j := by
  apply Fin.ext
  show (((j : ℕ) : ℤ) % (L : ℤ)).toNat = (j : ℕ)
  have h1 : ((j : ℕ) : ℤ) % (L : ℤ) = ((j : ℕ) : ℤ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast j.isLt)
  rw [h1, Int.toNat_natCast]

/-- A two-level tree: the `L`-split with class `j` split by `k j`. -/
theorem ty_node {L : ℕ} (hL : 2 ≤ L) (k : Fin L → ℕ) (hk : ∀ j, 2 ≤ k j) :
    Ty (∑ j, (ml (tail [k j])).map (place (child L j))) L (∑ j, {k j}) := by
  have hL0 : 0 < L := by omega
  let kf : Box → ℕ := fun E => k (classOf L hL0 E.r)
  have hkf : ∀ j, kf (child L j) = k j := fun j => congrArg k (classOf_child hL0 j)
  have h := (Ty.chain hL (l := []) (by simp)).bind (fun E => ml (tail [kf E])) kf (fun _ => 0)
    (fun E _ => (Ty.chain (hk (classOf L hL0 E.r)) (l := []) (by simp)).congr2 rfl Multiset.coe_nil)
  refine h.congr2 ?_ ?_
  · rw [ml_tail_single_sum L, fsum_bind]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Multiset.singleton_bind, hkf]
  · rw [ml_tail_single_sum L, fsum_bind, Multiset.coe_nil, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Multiset.singleton_bind, hkf, Multiset.cons_zero]

theorem forall₂_flatMap {α : Type*} {R : Box → Box → Prop} {f g : α → List Box} :
    ∀ {l : List α}, (∀ a ∈ l, List.Forall₂ R (f a) (g a)) →
      List.Forall₂ R (l.flatMap f) (l.flatMap g)
  | [], _ => .nil
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h a List.mem_cons_self)
      (forall₂_flatMap fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The source boxes: class `j` mod `L` split by `k j`. -/
def srcList (L : ℕ) (k : Fin L → ℕ) : List Box :=
  (List.finRange L).flatMap fun j => (tail [k j]).leaves.map (place (child L j))

/-- The target boxes: the box `B j` split by `k j`. -/
def tgtList (L : ℕ) (k : Fin L → ℕ) (B : Fin L → Box) : List Box :=
  (List.finRange L).flatMap fun j => (tail [k j]).leaves.map (place (B j))

theorem IsPC.two_le {g : Perm ℤ} (hg : IsPC g) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ j : Fin L, ∃ B : Box, CanonOn g (child L j) B := by
  obtain ⟨L, hL, hB⟩ := hg
  refine ⟨2 * L, by omega, fun j => ?_⟩
  let jh : Fin L := ⟨j % L, Nat.mod_lt _ hL⟩
  let jg : Fin 2 := ⟨j / L, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.isLt (Nat.mul_comm _ _))⟩
  have hsplit : child (2 * L) j = place (child L jh) (child 2 jg) := by
    ext
    · simp only [child_r, place_r, child_m, jh, jg]
      push_cast
      exact_mod_cast (Nat.mod_add_div' (j : ℕ) L).symm
    · simp only [child_m, place_m]
      push_cast
      ring
  obtain ⟨B, hB'⟩ := hB jh
  refine ⟨place B (child 2 jg), ?_⟩
  rw [hsplit]
  exact hB'.place (child 2 jg)

/-- **Every piecewise-canonical permutation lies in `CT(ℤ)`.** -/
theorem mem_ct_of_isPC {g : Perm ℤ} (hg : IsPC g) : g ∈ classTranspositionGroup := by
  obtain ⟨L, hL, hB⟩ := hg.two_le
  choose B hB using hB
  have hL0 : 0 < L := by omega
  have hdisjB : ∀ i j, i ≠ j → (B i).Disj (B j) := fun i j hij n hi hj =>
    child_disj L hij _ ((hB i).inv.mem hi) ((hB j).inv.mem hj)
  have hcovB : ∀ n, ∃ j, (B j).Mem n := fun n => by
    refine ⟨classOf L hL0 (g⁻¹ n), ?_⟩
    have := (hB (classOf L hL0 (g⁻¹ n))).mem (mem_classOf L hL0 (g⁻¹ n))
    simpa only [Perm.coe_inv, Equiv.apply_symm_apply] using this
  obtain ⟨N, k, hk2, hkm⟩ : ∃ (N : ℕ) (k : Fin L → ℕ), (∀ j, 2 ≤ k j) ∧
      ∀ j, (k j : ℤ) * (B j).m = N := by
    have hpos : 0 < ∏ j, (B j).m.toNat :=
      Finset.prod_pos fun j _ => by have := (B j).m_pos; omega
    have hdvd : ∀ j, ∃ c : ℕ, ∏ i, (B i).m.toNat = (B j).m.toNat * c :=
      fun j => Finset.dvd_prod_of_mem (fun i => (B i).m.toNat) (Finset.mem_univ j)
    choose c hc using hdvd
    refine ⟨2 * ∏ i, (B i).m.toNat, fun j => 2 * c j, fun j => ?_, fun j => ?_⟩
    · have h0 : 0 < c j := by
        rcases Nat.eq_zero_or_pos (c j) with h | h
        · have := hc j
          rw [h, mul_zero] at this
          omega
        · exact h
      exact (by omega : 2 ≤ 2 * c j)
    · have h2 : (((B j).m.toNat : ℕ) : ℤ) = (B j).m := Int.toNat_of_nonneg (B j).m_pos.le
      rw [hc j]
      simp only [Nat.cast_mul, Nat.cast_ofNat, h2]
      ring
  have hN2 : 2 ≤ N := by
    have h1 := hkm ⟨0, hL0⟩
    have h2 : (2 : ℤ) ≤ k ⟨0, hL0⟩ := by exact_mod_cast hk2 ⟨0, hL0⟩
    have h3 := (B ⟨0, hL0⟩).m_pos
    have : (2 : ℤ) ≤ N := by rw [← h1]; nlinarith
    exact_mod_cast this
  have hf : List.Forall₂ (CanonOn g) (srcList L k) (tgtList L k B) := by
    unfold srcList tgtList
    exact forall₂_flatMap fun j _ => forall₂_canon_map (hB j) _
  have hdl : (tgtList L k B).Pairwise Box.Disj := by
    rw [tgtList, List.pairwise_flatMap]
    refine ⟨fun j _ => ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (pairwise (tail [k j])).imp fun h => disj_place h
    · refine List.Pairwise.imp (fun {i j} hij => ?_) (List.nodup_finRange L)
      intro x hx y hy
      obtain ⟨X, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hy
      exact disj_place_of (hdisjB i j hij)
  have hcov : ∀ n, ∃ D ∈ tgtList L k B, D.Mem n := by
    intro n
    obtain ⟨j, hj⟩ := hcovB n
    obtain ⟨X, hX, hXn⟩ := cover (tail [k j]) (wf_tail (by simpa using hk2 j)) (n / (B j).m)
    refine ⟨place (B j) X, ?_, mem_place.2 ⟨hj, hXn⟩⟩
    unfold tgtList
    exact List.mem_flatMap.2 ⟨j, List.mem_finRange j, List.mem_map.2 ⟨X, hX, rfl⟩⟩
  have hdT : (tgtList L k B : Multiset Box) = ml (tail [N]) := by
    rw [Multiset.Nodup.ext (Multiset.coe_nodup.2 (hdl.imp fun h => ne_of_disj h)) (pd_ml _).nodup]
    intro x
    rw [Multiset.mem_coe, mem_ml_tail_single, tgtList, List.mem_flatMap]
    constructor
    · rintro ⟨j, -, hx⟩
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hx
      have hXm : X.m = k j := mem_ml_tail_single.1 (Multiset.mem_coe.2 hX)
      rw [place_m, hXm, hkm j]
    · intro hx
      obtain ⟨j, hj⟩ := hcovB x.r
      obtain ⟨Y, hY⟩ := eq_place hj ⟨k j, by rw [hx, ← hkm j, mul_comm]⟩
      have hYm : Y.m * (B j).m = (k j : ℤ) * (B j).m := by
        rw [hkm j, ← hx]
        exact (congrArg Box.m hY).symm
      refine ⟨j, List.mem_finRange j, List.mem_map.2 ⟨Y, ?_, hY.symm⟩⟩
      exact Multiset.mem_coe.1 (mem_ml_tail_single.2 (mul_right_cancel₀ (B j).m_ne hYm))
  have hcS : (srcList L k : Multiset Box) = ∑ j, (ml (tail [k j])).map (place (child L j)) := by
    rw [srcList, coe_flatMap, Fin.sum_univ_def]
    rfl
  have hTS : Ty (srcList L k : Multiset Box) L (∑ j, {k j}) := (ty_node hL k hk2).congr2 hcS.symm rfl
  have hTT : Ty (tgtList L k B : Multiset Box) N 0 := by
    rw [hdT]
    exact (Ty.chain hN2 (l := []) (by simp)).congr2 rfl Multiset.coe_nil
  refine mem_ct_of_canon hf hdl hcov (hTS.meq_of_card hTT ?_)
  rw [Multiset.coe_card, Multiset.coe_card]
  exact hf.length_eq

/-- **Kourovka 17.59** (S. Kohl): `CT(ℤ)` is exactly the group of residue-class-wise affine
permutations of `ℤ` that fix the nonnegative integers setwise. -/
theorem kourovka_17_59 :
    (classTranspositionGroup : Set (Equiv.Perm ℤ)) =
      {g | IsResidueClassWiseAffine g ∧ ∀ n : ℤ, 0 ≤ n ↔ 0 ≤ g n} := by
  ext g
  constructor
  · intro hg
    have hpc : IsPC g := ct_le_pc hg
    exact ⟨hpc.rcwa, hpc.sign⟩
  · rintro ⟨h1, h2⟩
    exact mem_ct_of_isPC (isPC_of_rcwa h1 h2)

end GroupApproximation.Kourovka1759
