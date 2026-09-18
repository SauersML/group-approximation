import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderList
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinchOrder.OrderOrbit
import GroupApproximation.Meta.AxiomGuard

/-!
# The outer walk reads the walk backwards

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `w` be a noncrossing closed walk in a planar map `M` whose inner reclosing keeps the Euler
characteristic, and let `x₀` be a dart of the walk map whose reversal is the last dart of `w`.
The face orbit `lakeWalk M w x₀` of `x₀`, reversed and with every dart reversed, is a sublist
of `w` (`lakeWalk_reverse_map_alpha_sublist`).

Proof.  Let `L_i` be the darts of the orbit, and `q_i` the position of `α L_i` on `w`.  Then
`q_0` is the last position.  If `j < k` and `q_j < q_k`, the three darts `L_0, L_j, L_k` of the
ring map `ordRing` (a planar map, `ordRing_planar`) contradict the theta obstruction
`false_of_theta`: the face orbit of `L_0` meets `L_j` and then `L_k`, and the face orbit of the
walk darts meets `α L_0 = w[last]`, `α L_j = w[q_j]`, `α L_k = w[q_k]` in this cyclic order
(`ord_false_of_cross`).  So `q` strictly decreases (`ord_pos_lt`), and the sublist property
follows (`reverse_map_sublist_of_pos`).
-/

namespace GroupApproximation.Full.GL03BPinchOrder

universe u

open Equiv
open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFill

/-- Composing powers of a permutation. -/
theorem ord_pow_add_apply {α : Type*} (f : Perm α) (m n : ℕ) (x : α) :
    (f ^ m) ((f ^ n) x) = (f ^ (m + n)) x := by
  rw [pow_add, Perm.mul_apply]

/-- The zeroth power of a permutation. -/
theorem ord_pow_zero_apply {α : Type*} (f : Perm α) (x : α) : (f ^ 0) x = x := by
  rw [pow_zero, Perm.one_apply]

variable {M : CombMap.{u}} {w : List M.Dart}

/-- Distinct powers below the period give distinct darts of the lake orbit. -/
theorem ord_lake_ne (x₀ : (walkMap M w).Dart) {s t : ℕ}
    (hs : s < period (walkMap M w).facePerm x₀) (ht : t < period (walkMap M w).facePerm x₀)
    (hne : s ≠ t) :
    (((walkMap M w).facePerm ^ s) x₀).1 ≠ (((walkMap M w).facePerm ^ t) x₀).1 :=
  fun h => hne (pow_apply_inj _ _ hs ht (Subtype.ext h))

/-- The darts of the lake orbit are not on `w`. -/
theorem ord_lake_not_mem (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) (hx₀ : M.alpha x₀.1 ∈ w) (t : ℕ) :
    (((walkMap M w).facePerm ^ t) x₀).1 ∉ w :=
  fun h => hw.alpha_not_mem _ h (lake_orbit hw hM x₀ hx₀ t).2

/-- The reversal of a lake dart of the ring map is the walk dart at its position. -/
theorem ord_alpha_X_eq_wd (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) (hx₀ : M.alpha x₀.1 ∈ w) (i r : ℕ) (hr : r < w.length)
    (h : w[r] = M.alpha (((walkMap M w).facePerm ^ i) x₀).1) :
    (ordRing hw hM).alpha (((ordRing hw hM).facePerm ^ i) (lakeStart hw hM x₀)) =
      wd hw hM r hr :=
  ordRing_ext hw hM ((congrArg M.alpha (lake_orbit hw hM x₀ hx₀ i).1).trans h.symm)

/-- A ring-map dart whose underlying dart differs from the six underlying darts is not one of the
six darts. -/
theorem not_sixDart_of_val (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {A B C z : (ordRing hw hM).Dart} (h1 : z.1.1 ≠ A.1.1) (h2 : z.1.1 ≠ B.1.1)
    (h3 : z.1.1 ≠ C.1.1) (h4 : z.1.1 ≠ M.alpha A.1.1) (h5 : z.1.1 ≠ M.alpha B.1.1)
    (h6 : z.1.1 ≠ M.alpha C.1.1) : ¬ SixDart (ordRing hw hM) A B C z := by
  rintro (h | h | h | h | h | h)
  · exact h1 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)
  · exact h2 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)
  · exact h3 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)
  · exact h4 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)
  · exact h5 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)
  · exact h6 (congrArg (fun x : (ordRing hw hM).Dart => x.1.1) h)

/-- A first hit along the walk darts of the ring map. -/
theorem firstHit_wd (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (S : (ordRing hw hM).Dart → Prop) (t m : ℕ) (ht : t < w.length) (hm : m < w.length)
    (htm : t < m)
    (hskip : ∀ r (hr : r < w.length), t < r → r < m → ¬ S (wd hw hM r hr)) :
    FirstHit (ordRing hw hM).facePerm S (wd hw hM t ht) (wd hw hM m hm) := by
  refine ⟨m - t, by omega, ?_, fun s hs0 hsm => ?_⟩
  · exact (ordRing_facePerm_pow_wd hw hM t (m - t) ht (by omega)).trans
      (ordRing_ext hw hM (getElem_idx_congr w (i := t + (m - t)) (j := m) (by omega)
        (by omega) hm))
  · rw [ordRing_facePerm_pow_wd hw hM t s ht (by omega)]
    exact hskip (t + s) (by omega) (by omega) (by omega)

/-- A first hit along the lake orbit of the ring map. -/
theorem firstHit_lake (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (x₀ : (walkMap M w).Dart) (S : (ordRing hw hM).Dart → Prop) (i m : ℕ) (him : i < m)
    (hskip : ∀ r, i < r → r < m →
      ¬ S (((ordRing hw hM).facePerm ^ r) (lakeStart hw hM x₀))) :
    FirstHit (ordRing hw hM).facePerm S (((ordRing hw hM).facePerm ^ i) (lakeStart hw hM x₀))
      (((ordRing hw hM).facePerm ^ m) (lakeStart hw hM x₀)) := by
  refine ⟨m - i, by omega, ?_, fun t ht0 htm => ?_⟩
  · rw [ord_pow_add_apply, Nat.sub_add_cancel him.le]
  · rw [ord_pow_add_apply]
    exact hskip (t + i) (by omega) (by omega)
