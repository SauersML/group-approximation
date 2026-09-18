import GroupApproximation.GGT.VanKampen.PermFirstReturnOrbits
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-61: iterating a first return

Lane gl-p07-61.  Certifies no printed sentence on its own.  NOT COMPILED.

* `witnessStepBridge_firstReturn_iterate`: let `q` be the first-return permutation of `p` on the
  image of `e`.  If `p ^ m` sends `e b` to `e b'` with `m > 0`, then some `q ^ m'` with `m' > 0`
  sends `b` to `b'`.  Every intermediate `q`-iterate is some intermediate `p`-iterate.
* `witnessStepBridge_inv_pow_apply`: `f⁻¹ ^ k` undoes the first `k` steps of `f ^ (k + r)`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u v

namespace FourPieceWitness

/-- `f⁻¹ ^ k` undoes the first `k` steps of `f ^ (k + r)`. -/
theorem witnessStepBridge_inv_pow_apply {A : Type u} (f : Equiv.Perm A) (k r : ℕ) (z : A) :
    (f⁻¹ ^ k) ((f ^ (k + r)) z) = (f ^ r) z := by
  rw [inv_pow, Equiv.Perm.inv_eq_iff_eq, pow_add, Equiv.Perm.mul_apply]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_inv_pow_apply

/-- **An ambient return to the image is an iterate of the first return.**  The intermediate
iterates of the first return are intermediate ambient iterates. -/
theorem witnessStepBridge_firstReturn_iterate {A : Type u} {B : Type v} {p : Equiv.Perm A}
    {q : Equiv.Perm B} {e : B ↪ A} (h : PermFirstReturn.IsFirstReturn p q e) (m : ℕ) :
    ∀ b b' : B, 0 < m → (p ^ m) (e b) = e b' →
      ∃ m', 0 < m' ∧ (q ^ m') b = b' ∧
        ∀ k, 0 < k → k < m' → ∃ j, 0 < j ∧ j < m ∧ e ((q ^ k) b) = (p ^ j) (e b) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro b b' hm hpb
    obtain ⟨m₁, hm₁, hq, hnot⟩ := h b
    rcases lt_trichotomy m m₁ with hlt | heq | hgt
    · exact absurd (Set.mem_range.mpr ⟨b', hpb.symm⟩) (hnot m hm hlt)
    · subst heq
      refine ⟨1, Nat.one_pos, ?_, fun k hk hk1 => absurd hk (by omega)⟩
      rw [pow_one]
      exact e.injective (hq.symm.trans hpb)
    · have hm₂ : 0 < m - m₁ := by omega
      have hstep : (p ^ (m - m₁)) (e (q b)) = e b' := by
        rw [← hq, ← Equiv.Perm.mul_apply (p ^ (m - m₁)) (p ^ m₁), ← pow_add,
          Nat.sub_add_cancel hgt.le]
        exact hpb
      obtain ⟨m'', -, hq'', hmid⟩ := ih (m - m₁) (by omega) (q b) b' hm₂ hstep
      refine ⟨m'' + 1, by omega, ?_, ?_⟩
      · rw [pow_succ, Equiv.Perm.mul_apply]
        exact hq''
      · intro k hk hkm
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · refine ⟨m₁, hm₁, hgt, ?_⟩
          have hk1 : k = 1 := by omega
          subst hk1
          rw [pow_one]
          exact hq.symm
        · obtain ⟨j, -, hjm, hje⟩ := hmid (k - 1) (by omega) (by omega)
          refine ⟨j + m₁, by omega, by omega, ?_⟩
          have hk' : k = (k - 1) + 1 := by omega
          rw [hk', pow_succ, Equiv.Perm.mul_apply, hje, pow_add, Equiv.Perm.mul_apply, hq]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepBridge_firstReturn_iterate

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
