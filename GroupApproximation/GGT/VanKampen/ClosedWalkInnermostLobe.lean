import GroupApproximation.GGT.VanKampen.ClosedWalkPinchSplit
import Mathlib.Data.List.Nodup
import GroupApproximation.Meta.AxiomGuard

/-!
# The innermost lobe of a walk at its first repeated vertex

A walk that repeats a vertex has a window, between two visits of one vertex, that is a closed
dart walk with no repeated vertex: take the first position `j` at which the vertex of the dart at
`j` already occurred, at some position `i < j`.  The darts from `i` up to `j` form the window.  It
closes because the dart before `j` ends at the vertex of `j`, which is the vertex of `i`, and it
repeats no vertex because it lies in the prefix before `j`, which repeats none.

* `exists_first_repeat`: the first repeat of a list under a map.
* `isClosedDartWalk_window`: the window between two visits of one vertex is a closed dart walk.
* `exists_innermost_lobe`: a walk that repeats a vertex splits as `l₁ ++ L ++ l₂` with `L` a closed
  dart walk repeating no vertex.
* `isSimpleClosedWalk_of_nodup`: a closed dart walk of length at least three that repeats no
  vertex is simple.  A dart and its reverse on it would be consecutive in both orders, which forces
  length at most two.  Lobes of length one or two are loops, digons and hairs `[d, alpha d]`.

These are the lobes excised from the pinched pocket walks of Lemma 9.4, Case 1
(`OsinLemma94CaseOneCellPinchStatement`, a vertex repeated on the carrier part of the walk).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen
namespace ClosedWalkInnermostLobe

universe v

/-- **The first repeat of a list under a map.**  If `l.map f` has a repeated value, there are
positions `i < j` with `f l[i] = f l[j]` such that the prefix of length `j` has no repeated value. -/
theorem exists_first_repeat {α β : Type*} (f : α → β) {l : List α} (h : ¬ (l.map f).Nodup) :
    ∃ (i j : ℕ) (_hij : i < j) (hj : j < l.length),
      f l[i] = f l[j] ∧ ((l.take j).map f).Nodup := by
  classical
  have hex : ∃ n, ¬ ((l.take n).map f).Nodup :=
    ⟨l.length, by rwa [List.take_of_length_le (le_refl l.length)]⟩
  have hn := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ((l.take m).map f).Nodup := fun m hm =>
    not_not.mp (Nat.find_min hex hm)
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hn
    exact hn (by simp)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hj] at hn
  have hjnodup : ((l.take j).map f).Nodup := hmin j (by omega)
  have hjlen : j < l.length := by
    by_contra hge
    rw [List.take_of_length_le (show l.length ≤ j + 1 by omega)] at hn
    rw [List.take_of_length_le (show l.length ≤ j by omega)] at hjnodup
    exact hn hjnodup
  have hexi : ∃ i, ∃ _hij : i < j, f l[i] = f l[j] := by
    by_contra hno
    apply hn
    rw [List.take_succ_eq_append_getElem hjlen, List.map_append, List.map_singleton]
    refine List.nodup_append.mpr ⟨hjnodup, List.nodup_singleton _, ?_⟩
    intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.mp hx
    exact hno ⟨k, by omega, hab⟩
  obtain ⟨i, hij, hrep⟩ := hexi
  exact ⟨i, j, hij, hjlen, hrep, hjnodup⟩

/-- **The window between two visits of one vertex is a closed dart walk.** -/
theorem isClosedDartWalk_window {M : CombMap.{v}} {l : List M.Dart}
    (hchain : l.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    {i j : ℕ} (hij : i < j) (hj : j < l.length)
    (hrep : M.vertexOf l[i] = M.vertexOf l[j]) :
    IsClosedDartWalk M ((l.drop i).take (j - i)) := by
  have hchain' := List.isChain_iff_getElem.mp hchain
  have hlen : ((l.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  have hne : (l.drop i).take (j - i) ≠ [] := by
    intro h
    have h' := congrArg List.length h
    rw [hlen, List.length_nil] at h'
    omega
  refine ⟨hne, List.isChain_iff_getElem.mpr fun k hk => ?_, ?_⟩
  · have hk' : i + k + 1 < l.length := by
      rw [hlen] at hk
      omega
    simpa only [List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchain' (i + k) hk'
  · have h := hchain' (j - 1) (by omega)
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    have hidx : i + (j - i - 1) = j - 1 := by omega
    have hidx2 : j - 1 + 1 = j := by omega
    simp only [List.getElem_take, List.getElem_drop, hlen, hidx, Nat.add_zero]
    simp only [hidx2] at h
    exact h.trans hrep.symm

/-- **The innermost lobe.**  A walk that repeats a vertex splits as `l₁ ++ L ++ l₂`, where `L` is a
closed dart walk repeating no vertex. -/
theorem exists_innermost_lobe {M : CombMap.{v}} {l : List M.Dart}
    (hchain : l.IsChain fun d e => M.vertexOf (M.alpha d) = M.vertexOf e)
    (hrep : ¬ (l.map M.vertexOf).Nodup) :
    ∃ l₁ L l₂ : List M.Dart, l = l₁ ++ L ++ l₂ ∧ IsClosedDartWalk M L ∧
      (L.map M.vertexOf).Nodup := by
  obtain ⟨i, j, hij, hj, hvij, hnodup⟩ := exists_first_repeat M.vertexOf hrep
  refine ⟨l.take i, (l.drop i).take (j - i), l.drop j, ?_,
    isClosedDartWalk_window hchain hij hj hvij, ?_⟩
  · conv_lhs => rw [← List.take_append_drop i l, ← List.take_append_drop (j - i) (l.drop i)]
    rw [List.drop_drop, show i + (j - i) = j by omega, List.append_assoc]
  · rw [← List.drop_take]
    exact List.Nodup.sublist (List.Sublist.map _ (List.drop_sublist _ _)) hnodup

/-- **A closed dart walk of length at least three repeating no vertex is simple.**  If a dart `d`
and its reverse are both on the walk, the reverse starts where `d` ends and ends where `d` starts,
so each follows the other on the cycle of positions, which has length at most two. -/
theorem isSimpleClosedWalk_of_nodup {M : CombMap.{v}} {L : List M.Dart}
    (hw : IsClosedDartWalk M L) (hnodup : (L.map M.vertexOf).Nodup) (hlen : 3 ≤ L.length) :
    IsSimpleClosedWalk M L := by
  obtain ⟨hne, hchain, hclose⟩ := hw
  refine ⟨hne, hchain, hclose, hnodup, ?_⟩
  intro d hd hαd
  have hchain' := List.isChain_iff_getElem.mp hchain
  have hinj : ∀ (a b : ℕ) (ha : a < L.length) (hb : b < L.length),
      M.vertexOf L[a] = M.vertexOf L[b] → a = b := by
    intro a b ha hb hab
    have hmap : (L.map M.vertexOf)[a]'(by simpa using ha)
        = (L.map M.vertexOf)[b]'(by simpa using hb) := by
      simpa only [List.getElem_map] using hab
    exact (List.Nodup.getElem_inj_iff hnodup).mp hmap
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨q, hq, hqp⟩ := List.getElem_of_mem hαd
  have hvq : M.vertexOf (M.alpha L[p]) = M.vertexOf L[q] := by rw [hqp]
  have hvp : M.vertexOf (M.alpha L[q]) = M.vertexOf L[p] := by
    rw [hqp, M.alpha_involutive L[p]]
  rw [List.getLast_eq_getElem, List.head_eq_getElem] at hclose
  by_cases hp1 : p + 1 < L.length
  · have hq1 : q = p + 1 := hinj q (p + 1) hq hp1 (hvq.symm.trans (hchain' p hp1))
    subst hq1
    by_cases hq2 : p + 1 + 1 < L.length
    · have := hinj p (p + 1 + 1) hp hq2 (hvp.symm.trans (hchain' (p + 1) hq2))
      omega
    · have hlast : p + 1 = L.length - 1 := by omega
      have h0 : M.vertexOf (M.alpha L[p + 1]) = M.vertexOf L[0] := by
        simpa only [hlast] using hclose
      have := hinj p 0 hp (by omega) (hvp.symm.trans h0)
      omega
  · have hlast : p = L.length - 1 := by omega
    have h0 : M.vertexOf (M.alpha L[p]) = M.vertexOf L[0] := by
      simpa only [hlast] using hclose
    have hq0 : q = 0 := hinj q 0 hq (by omega) (hvq.symm.trans h0)
    subst hq0
    have := hinj p (0 + 1) hp (by omega) (hvp.symm.trans (hchain' 0 (by omega)))
    omega

end ClosedWalkInnermostLobe
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe.exists_first_repeat
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe.isClosedDartWalk_window
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe.exists_innermost_lobe
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkInnermostLobe.isSimpleClosedWalk_of_nodup
