import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkPassageDichotomy
import GroupApproximation.Meta.AxiomGuard

/-!
# At a vertex all passages turn the same way

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b): "Let us consider the subdiagram `Γ_1` of `Δ`
such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2` ... (ii) `Γ_1` contains all `Γ_{i,1}`'s."

Let `w` be a noncrossing closed walk whose passages have free sectors.  The passage at position `i`
is *adjacent* when the stretch from `w[i+1]` back to `alpha w[i]` is free
(`SectorNoninterleaving.PassageAdjacent`); otherwise its sector from `alpha w[i]` to `w[i+1]` is free.
Rotating from a walk dart `e`, the first dart on an edge of the walk is the reversal of a walk dart
(`IsNoncrossingClosedWalk.exists_first_alpha_after`), since the darts in between stay outside the side
of the walk.  If the passage at `j` is not adjacent, rotation from `alpha w[j]` passes its free sector
to `w[j+1]` and then the free stretch to the next reversal `alpha w[l]`.  An adjacent passage there
would be the passage at `j` itself (`SectorNoninterleaving.eq_of_adjacent_of_free`).  By induction along
the rotation, no adjacent passage lies at the vertex of a passage that is not adjacent
(`IsNoncrossingClosedWalk.passageAdjacent_of_vertex`).

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open Equiv SimpleClosedWalkSides SectorNoninterleaving

universe u

namespace SectorNoninterleaving

/-- **An adjacent passage**: the stretch from `w[i+1]` back to `alpha w[i]` is free of the walk. -/
def PassageAdjacent (M : CombMap.{u}) (w : List M.Dart) (i : Fin w.length) : Prop :=
  SectorFree M w (w.get (finRotate w.length i)) (M.alpha (w.get i))

end SectorNoninterleaving

namespace IsNoncrossingClosedWalk

variable {M : CombMap.{u}} {w : List M.Dart}

private theorem pow_add_apply (M : CombMap.{u}) (m a : ℕ) (x : M.Dart) :
    (M.sigma ^ (m + a)) x = (M.sigma ^ m) ((M.sigma ^ a) x) := by
  rw [pow_add, Perm.mul_apply]

/-- **The first dart on an edge of the walk after a walk dart is the reversal of a walk dart.** -/
theorem exists_first_alpha_after (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    {e : M.Dart} (he : e ∈ w) :
    ∃ l : Fin w.length, ∃ b : ℕ, 0 < b ∧ (M.sigma ^ b) e = M.alpha (w.get l) ∧
      ∀ k, 0 < k → k < b → ¬ walkKeep M w ((M.sigma ^ k) e) := by
  classical
  have hex : ∃ b, 0 < b ∧ walkKeep M w ((M.sigma ^ b) e) := by
    obtain ⟨p, hp⟩ := ((M.vertexOf_eq_iff (M.sigma e) e).mp (M.vertexOf_sigma e)).exists_nat_pow_eq
    exact ⟨p + 1, Nat.succ_pos p, Or.inl (by rw [pow_succ, Perm.mul_apply, hp]; exact he)⟩
  obtain ⟨b, ⟨hb0, hbk⟩, hmin⟩ : ∃ b, (0 < b ∧ walkKeep M w ((M.sigma ^ b) e)) ∧
      ∀ b' < b, ¬ (0 < b' ∧ walkKeep M w ((M.sigma ^ b') e)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ h => Nat.find_min hex h⟩
  have hfree : ∀ k, 0 < k → k < b → ¬ walkKeep M w ((M.sigma ^ k) e) :=
    fun k hk hkb h => hmin k hkb ⟨hk, h⟩
  have hout1 : M.faceOf (M.sigma e) ∉ sideFaces M w := by
    rw [faceOf_sigma M e]
    exact hw.faceOf_alpha_not_mem_of_mem hM he
  have hzout : M.faceOf ((M.sigma ^ b) e) ∉ sideFaces M w := by
    rcases Nat.lt_or_ge 1 b with h1 | h1
    · have hya : M.alpha (M.sigma e) ∉ w := fun h =>
        hfree 1 Nat.one_pos h1 (Or.inr (by rw [pow_one]; exact h))
      have hstep := hw.faceOf_sigma_pow_not_mem_of_free hM (m := b - 1) hout1 hya
        (fun k hk hkb => by
          have h' := hfree (k + 1) (by omega) (by omega)
          rwa [pow_succ, Perm.mul_apply] at h') (b - 1) le_rfl
      have hb' : (M.sigma ^ (b - 1)) (M.sigma e) = (M.sigma ^ b) e := by
        rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ b)]
      rwa [hb'] at hstep
    · obtain rfl : b = 1 := by omega
      rw [pow_one]
      exact hout1
  have hza : M.alpha ((M.sigma ^ b) e) ∈ w := by
    rcases hbk with h | h
    · exact absurd (hw.faceOf_mem_of_mem hM h) hzout
    · exact h
  obtain ⟨l, hl⟩ := List.get_of_mem hza
  exact ⟨l, b, hb0, by rw [hl, M.alpha_involutive], hfree⟩

/-- **An adjacent passage makes every passage at its vertex adjacent.** -/
theorem passageAdjacent_of_vertex (hw : IsNoncrossingClosedWalk M w) (hM : M.IsPlanar)
    (hsector : ∀ i : Fin w.length,
      PassageSectorFree M w (w.get i) (w.get (finRotate w.length i)))
    {i j : Fin w.length} (hi : PassageAdjacent M w i)
    (hv : M.vertexOf (M.alpha (w.get j)) = M.vertexOf (M.alpha (w.get i))) :
    PassageAdjacent M w j := by
  classical
  have hmem : ∀ k : Fin w.length, w.get k ∈ w := fun k => List.get_mem w k
  have hkeepi : walkKeep M w (M.alpha (w.get i)) :=
    Or.inr (by rw [M.alpha_involutive]; exact hmem i)
  have hinj : ∀ {a b : Fin w.length}, M.alpha (w.get a) = M.alpha (w.get b) → a = b := fun h =>
    hw.nodup.get_inj_iff.mp (M.alpha.injective h)
  suffices key : ∀ n (j : Fin w.length), (M.sigma ^ n) (M.alpha (w.get j)) = M.alpha (w.get i) →
      ¬ PassageAdjacent M w j → False by
    by_contra hj
    obtain ⟨n, hn⟩ := ((M.vertexOf_eq_iff _ _).mp hv).exists_nat_pow_eq
    exact key n j hn hj
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hn hj
    rcases hsector j with hshort | hadj
    · obtain ⟨a, ha, hafree⟩ := hshort
      obtain ⟨l, b, hb0, hbl, hbfree⟩ := hw.exists_first_alpha_after hM (hmem (finRotate _ j))
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · rw [hn0, pow_zero, Perm.one_apply] at hn
        exact hj (hinj hn ▸ hi)
      rcases Nat.lt_or_ge n a with hna | hna
      · exact hafree n hn0 hna (by rw [hn]; exact hkeepi)
      rcases Nat.eq_or_lt_of_le hna with hna | hna
      · subst hna
        rw [ha] at hn
        exact hw.alpha_not_mem _ (hmem i) (by rw [← hn]; exact hmem _)
      have hsplit : (M.sigma ^ n) (M.alpha (w.get j)) =
          (M.sigma ^ (n - a)) (w.get (finRotate _ j)) := by
        rw [← ha, ← pow_add_apply, Nat.sub_add_cancel hna.le]
      rw [hsplit] at hn
      have hfreeJ : SectorFree M w (w.get (finRotate _ j)) (M.alpha (w.get l)) := ⟨b, hbl, hbfree⟩
      rcases Nat.lt_or_ge (n - a) b with hnb | hnb
      · exact hbfree (n - a) (by omega) hnb (by rw [hn]; exact hkeepi)
      rcases Nat.eq_or_lt_of_le hnb with hnb | hnb
      · rw [← hnb, hbl] at hn
        obtain rfl := hinj hn
        exact hj (eq_of_adjacent_of_free hw.nodup hw.alpha_not_mem hi hfreeJ ▸ hi)
      · have hsplit2 : (M.sigma ^ (n - a)) (w.get (finRotate _ j)) =
            (M.sigma ^ (n - a - b)) (M.alpha (w.get l)) := by
          rw [← hbl, ← pow_add_apply, Nat.sub_add_cancel hnb.le]
        rw [hsplit2] at hn
        by_cases hl : PassageAdjacent M w l
        · exact hj (eq_of_adjacent_of_free hw.nodup hw.alpha_not_mem hl hfreeJ ▸ hl)
        · exact ih (n - a - b) (by omega) l hn hl
    · exact hj hadj

end IsNoncrossingClosedWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.exists_first_alpha_after
#audit_axioms GroupApproximation.GGT.VanKampen.IsNoncrossingClosedWalk.passageAdjacent_of_vertex
