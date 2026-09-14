import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEulerNoninterleaving
import GroupApproximation.Meta.AxiomGuard

/-!
# Passages with a free rotation sector do not interleave

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

`IsNoncrossingClosedWalk.eulers_of_noninterleaving` (`NoncrossingClosedWalkEulerNoninterleaving`)
keeps both Euler characteristics once the passages of a noncrossing closed walk do not interleave
(`PassagesNoninterleaving`).  The passage at position `i` is the chord from `alpha w[i]` to `w[i+1]`,
and its sector is the stretch of vertex rotation from `alpha w[i]` to `w[i+1]`.

The pocket walks `s_1 t_1 s_2 t_2` turn in two ways (sec2-sentences' hand argument).
* Along a side of a region, and at the four corners, the turn is a boundary step of the region: rotating
  from `alpha d` passes only internal darts of the region before the next dart.  So the sector holds no
  dart of the walk and no reverse of one.
* Along an arc of a cell or of the exterior, the turn is a face step, `σ (next d) = alpha d`, and the
  complementary stretch from the next dart back to `alpha d` is empty.

A passage with a free sector cannot interleave with another one.
* `SectorFree M w x y`: rotating from `x` reaches `y`, with no dart of `w`, and no reverse of one,
  strictly in between.  `PassageSectorFree M w d e`: the sector from `alpha d` to `e` or the one from `e`
  to `alpha d` is free.
* `sectorFree_of_sigma_eq`: a face step has a free stretch.
* `not_rotationBetween_of_sectorFree`: when the sector from `x` to `y` is free, no dart on an edge of the
  walk lies inside it.
* `rotationBetween_of_sectorFree_rev`: when the stretch from `y` to `x` is free, every other dart at the
  vertex on an edge of the walk lies inside the sector from `x` to `y`.
* `get_finRotate_of_isChain_closes`: a closing chain relates each position to the next one.
* `passagesNoninterleaving_of_forall_get`, `passagesNoninterleaving_of_isChain`,
  `IsNoncrossingClosedWalk.passagesNoninterleaving`: if every passage has a free sector, the passages
  do not interleave.  For a free sector both endpoints of any other passage are outside; for a free
  stretch back both are inside.

The hypothesis is needed.  In the rose with darts `0, …, 5`, `alpha = (0 1)(2 3)(4 5)` and
`sigma : 1 ↦ 0 ↦ 3 ↦ 2 ↦ 5 ↦ 4 ↦ 1`, the passage of `0` runs from `1` to `2`: its sector holds the
walk dart `0`, and the stretch back from `2` holds the walk dart `4`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides

universe u

namespace SectorNoninterleaving

/-- **A rotation sector free of the walk.**  Rotating from `x` reaches `y`, and no dart strictly in
between is a dart of `w` or the reverse of one. -/
def SectorFree (M : CombMap.{u}) (w : List M.Dart) (x y : M.Dart) : Prop :=
  ∃ m : ℕ, (M.sigma ^ m) x = y ∧ ∀ k, 0 < k → k < m → ¬ walkKeep M w ((M.sigma ^ k) x)

/-- **A passage with a free sector.**  The sector from `alpha d` to `e`, or the stretch from `e` back
to `alpha d`, is free of the walk. -/
def PassageSectorFree (M : CombMap.{u}) (w : List M.Dart) (d e : M.Dart) : Prop :=
  SectorFree M w (M.alpha d) e ∨ SectorFree M w e (M.alpha d)

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **A face step has a free stretch**: if rotation takes `y` to `x`, nothing lies strictly in
between. -/
theorem sectorFree_of_sigma_eq {x y : M.Dart} (h : M.sigma y = x) : SectorFree M w y x :=
  ⟨1, by rw [pow_one]; exact h, fun k hk hk1 => absurd hk1 (by omega)⟩

/-- **No dart on an edge of the walk inside a free sector.** -/
theorem not_rotationBetween_of_sectorFree {x y z : M.Dart} (h : SectorFree M w x y) (hxy : x ≠ y)
    (hz : walkKeep M w z) : ¬ RotationBetween M x y z := by
  rintro ⟨a, ha, haz, hay⟩
  obtain ⟨m, hm, hfree⟩ := h
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · rw [hm0, pow_zero, Equiv.Perm.one_apply] at hm
    exact hxy hm
  · rcases Nat.lt_or_ge a m with hlt | hge
    · exact hfree a ha hlt (by rw [haz]; exact hz)
    · exact hay m hm0 hge hm

/-- **Every other dart on an edge of the walk inside the sector, when the stretch back is free.**  If
the stretch from `y` to `x` is free of the walk, a dart `z` at the vertex of `x`, on an edge of the walk
and other than `x` and `y`, is reached from `x` before `y`. -/
theorem rotationBetween_of_sectorFree_rev {x y z : M.Dart} (h : SectorFree M w y x)
    (hv : M.vertexOf z = M.vertexOf x) (hz : walkKeep M w z) (hzx : z ≠ x) (hzy : z ≠ y) :
    RotationBetween M x y z := by
  classical
  obtain ⟨n, hn, hfree⟩ := h
  have hex : ∃ a : ℕ, (M.sigma ^ a) x = z :=
    ((M.vertexOf_eq_iff x z).mp hv.symm).exists_nat_pow_eq
  obtain ⟨a, haz, hmin⟩ : ∃ a : ℕ, (M.sigma ^ a) x = z ∧ ∀ a' < a, (M.sigma ^ a') x ≠ z :=
    ⟨Nat.find hex, Nat.find_spec hex, fun a' ha' => Nat.find_min hex ha'⟩
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero, Equiv.Perm.one_apply] at haz
      exact absurd haz.symm hzx
    · exact h0
  refine ⟨a, ha, haz, fun b hb hba hby => ?_⟩
  rcases Nat.lt_or_ge b a with hlt | hge
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
    have hc : (M.sigma ^ c) y = z := by
      rw [add_comm, pow_add, Equiv.Perm.mul_apply, hby] at haz
      exact haz
    rcases Nat.lt_trichotomy c n with hcn | hcn | hcn
    · exact hfree c (by omega) hcn (by rw [hc]; exact hz)
    · rw [hcn, hn] at hc
      exact hzx hc.symm
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hcn
      have he : (M.sigma ^ (e + 1)) x = z := by
        rw [show n + e + 1 = e + 1 + n by omega, pow_add, Equiv.Perm.mul_apply, hn] at hc
        exact hc
      exact hmin (e + 1) (by omega) he
  · have hab : b = a := le_antisymm hba hge
    rw [hab, haz] at hby
    exact hzy hby

/-- `finRotate n` moves a position to the next one, cyclically. -/
private theorem finRotate_val_eq_mod : ∀ {n : ℕ} (i : Fin n),
    (finRotate n i : ℕ) = (i.val + 1) % n
  | 0, i => i.elim0
  | n + 1, i => by
    rw [coe_finRotate]
    split_ifs with h
    · simp [h]
    · exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ (Fin.val_lt_last h))).symm

/-- **A closing chain relates each position to the next one.** -/
theorem get_finRotate_of_isChain_closes {α : Type*} {R : α → α → Prop} {l : List α}
    (hne : l ≠ []) (hchain : l.IsChain R) (hcloses : R (l.getLast hne) (l.head hne))
    (i : Fin l.length) : R (l.get i) (l.get (finRotate l.length i)) := by
  have hrot := finRotate_val_eq_mod i
  by_cases hlast : i.val + 1 < l.length
  · have heq : finRotate l.length i = ⟨i.val + 1, hlast⟩ :=
      Fin.ext (by rw [hrot, Nat.mod_eq_of_lt hlast])
    rw [heq]
    exact List.isChain_iff_getElem.mp hchain i.val hlast
  · have hpos : 0 < l.length := List.length_pos_iff.mpr hne
    have heq : finRotate l.length i = ⟨0, hpos⟩ :=
      Fin.ext (by rw [hrot, show i.val + 1 = l.length by omega, Nat.mod_self])
    rw [heq]
    obtain ⟨k, hk⟩ := i
    obtain rfl : k = l.length - 1 := by
      simp only at hlast
      omega
    have h := hcloses
    simp only [List.getLast_eq_getElem, List.head_eq_getElem] at h
    exact h

/-- **Passages with a free sector do not interleave.**  Let `w` be a duplicate-free walk using no edge
in both directions, each dart ending where the dart at the next position starts.  If every passage has
a free sector, the passages of `w` do not interleave. -/
theorem passagesNoninterleaving_of_forall_get (hnodup : w.Nodup)
    (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hnext : ∀ i : Fin w.length,
      M.vertexOf (M.alpha (w.get i)) = M.vertexOf (w.get (finRotate w.length i)))
    (hsector : ∀ i : Fin w.length,
      PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    PassagesNoninterleaving M w := by
  intro i j hij hv
  have hmem : ∀ k : Fin w.length, w.get k ∈ w := fun k => List.get_mem w k
  have hinj : ∀ {a b : Fin w.length}, w.get a = w.get b → a = b := fun h =>
    hnodup.get_inj_iff.mp h
  have hxy : M.alpha (w.get i) ≠ w.get (finRotate w.length i) := fun h =>
    halpha _ (hmem i) (by rw [h]; exact hmem _)
  have hk₁ : walkKeep M w (M.alpha (w.get j)) :=
    Or.inr (by rw [M.alpha_involutive (w.get j)]; exact hmem j)
  have hk₂ : walkKeep M w (w.get (finRotate w.length j)) := Or.inl (hmem _)
  rcases hsector i with hin | hout
  · exact iff_of_false (not_rotationBetween_of_sectorFree hin hxy hk₁)
      (not_rotationBetween_of_sectorFree hin hxy hk₂)
  · refine iff_of_true (rotationBetween_of_sectorFree_rev hout hv.symm hk₁ ?_ ?_)
      (rotationBetween_of_sectorFree_rev hout ((hnext j).symm.trans hv.symm) hk₂ ?_ ?_)
    · exact fun h => hij (hinj (M.alpha.injective h)).symm
    · exact fun h => halpha _ (hmem j) (by rw [h]; exact hmem _)
    · exact fun h => halpha _ (hmem i) (by rw [← h]; exact hmem _)
    · exact fun h => hij ((finRotate w.length).injective (hinj h.symm))

/-- **Passages with a free sector do not interleave, from a closing chain.** -/
theorem passagesNoninterleaving_of_isChain (hne : w ≠ []) (hnodup : w.Nodup)
    (halpha : ∀ d ∈ w, M.alpha d ∉ w)
    (hchain : w.IsChain fun d e =>
      M.vertexOf (M.alpha d) = M.vertexOf e ∧ PassageSectorFree M w d e)
    (hcloses : M.vertexOf (M.alpha (w.getLast hne)) = M.vertexOf (w.head hne) ∧
      PassageSectorFree M w (w.getLast hne) (w.head hne)) :
    PassagesNoninterleaving M w :=
  passagesNoninterleaving_of_forall_get hnodup halpha
    (fun i => (get_finRotate_of_isChain_closes hne hchain hcloses i).1)
    (fun i => (get_finRotate_of_isChain_closes hne hchain hcloses i).2)

end SectorNoninterleaving

namespace IsNoncrossingClosedWalk

open SectorNoninterleaving

variable {M : CombMap.{u}} {w : List M.Dart}

/-- **A noncrossing closed walk whose passages have free sectors has non-interleaving passages.** -/
theorem passagesNoninterleaving (hw : IsNoncrossingClosedWalk M w)
    (hsector : ∀ i : Fin w.length,
      PassageSectorFree M w (w.get i) (w.get (finRotate w.length i))) :
    PassagesNoninterleaving M w :=
  passagesNoninterleaving_of_forall_get hw.nodup hw.alpha_not_mem
    (fun i => get_finRotate_of_isChain_closes hw.ne_nil hw.chain hw.closes i) hsector

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.sectorFree_of_sigma_eq
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.not_rotationBetween_of_sectorFree
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.rotationBetween_of_sectorFree_rev
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.get_finRotate_of_isChain_closes
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.passagesNoninterleaving_of_forall_get
#audit_axioms GroupApproximation.GGT.VanKampen.SectorNoninterleaving.passagesNoninterleaving_of_isChain
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.passagesNoninterleaving
