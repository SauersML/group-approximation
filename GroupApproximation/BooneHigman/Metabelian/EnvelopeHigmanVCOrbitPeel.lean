import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Orbit peeling of antichain words (lane bh-met-77x)

Let `C` be a finite antichain and `r` a word in the letters of `C`, with leaf permutation
`π r = higmanVCOrbit_pi C r` of `C`.  By `higmanVCAll_lift_eq_one` (the transposition
presentation of `Sym(C)` holds in `Q`), the class of `ι r` depends only on `π r`.  This
lets us rewrite `ι r` one transposition `(x, π r x)` at a time, as in the swap-factor
algorithm.  Each peeled transposition stays inside one `π`-orbit.

* `higmanVCOrbit_mem_of_fix`: if `π r` fixes every leaf with property `p`, then `ι r` is a
  product of letters `(x, y)` with `¬ p x`, `¬ p y`.  So it lies in every subgroup `K`
  that contains those letters.
* `higmanVCOrbit_split`: if `π r` preserves the length of every leaf with property `p`,
  then `ι r = u * σ` with `u ∈ U` (balanced letters, peeled on the left) and `σ ∈ K`.
  Here `K` is as above.

Nothing here assumes Higman's theorem.  The only input is the proved faithfulness of the
transposition presentation on one antichain.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The leaf permutation `π` of a word in the letters of `C`. -/
noncomputable def higmanVCOrbit_pi {d : ℕ} (C : Finset (List (Fin d))) :
    FreeGroup (↥C × ↥C) →* Equiv.Perm ↥C :=
  FreeGroup.lift fun q : ↥C × ↥C => Equiv.swap q.1 q.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_pi

/-- `π` on a letter. -/
theorem higmanVCOrbit_pi_of {d : ℕ} (C : Finset (List (Fin d))) (q : ↥C × ↥C) :
    higmanVCOrbit_pi C (FreeGroup.of q) = Equiv.swap q.1 q.2 :=
  FreeGroup.lift_apply_of (f := fun q : ↥C × ↥C => Equiv.swap q.1 q.2)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_pi_of

/-- A word with trivial leaf permutation is trivial in `Q`. -/
theorem higmanVCOrbit_mk_eq_one {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) {r : FreeGroup (↥C × ↥C)}
    (hr : higmanVCOrbit_pi C r = 1) : higmanVCCommon_mk d (higmanVCAll_iota C r) = 1 := by
  show QuotientGroup.mk' (Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    (higmanVCAll_iota C r) = 1
  rw [higmanVCAll_mk_iota]
  exact higmanVCAll_lift_eq_one (higmanVCAll_gen d C) higmanVCAll_gen_self higmanVCAll_gen_sq
    (higmanVCAll_gen_conj hC) r hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_mk_eq_one

/-- Peeling one letter off the left of a word. -/
theorem higmanVCOrbit_mk_of_mul {d : ℕ} (C : Finset (List (Fin d))) (x y : ↥C)
    (r : FreeGroup (↥C × ↥C)) :
    higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of (x, y) * r)) =
      higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) *
        higmanVCCommon_mk d (higmanVCAll_iota C r) := by
  simp only [map_mul, higmanVCAll_iota_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_mk_of_mul

/-- **Fixed-set peeling.**  If `π r` fixes every leaf with property `p`, then `ι r` lies in
every subgroup containing the letters between leaves without `p`. -/
theorem higmanVCOrbit_mem_of_fix {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (p : ↥C → Prop) {K : Subgroup (higmanVCCommon_Q d)}
    (hK : ∀ x y : ↥C, ¬ p x → ¬ p y →
      higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) ∈ K) :
    ∀ (k : ℕ) (r : FreeGroup (↥C × ↥C)), (higmanVCOrbit_pi C r).support.card ≤ k →
      (∀ c, p c → higmanVCOrbit_pi C r c = c) →
        higmanVCCommon_mk d (higmanVCAll_iota C r) ∈ K := by
  intro k
  induction k with
  | zero =>
    intro r hk _
    rw [higmanVCOrbit_mk_eq_one hC (Equiv.Perm.card_support_eq_zero.mp (Nat.le_zero.mp hk))]
    exact K.one_mem
  | succ k ih =>
    intro r hk hfix
    by_cases h1 : higmanVCOrbit_pi C r = 1
    · rw [higmanVCOrbit_mk_eq_one hC h1]
      exact K.one_mem
    obtain ⟨x, hx⟩ : ∃ x, higmanVCOrbit_pi C r x ≠ x := by
      by_contra hne
      push Not at hne
      exact h1 (Equiv.ext fun c => (hne c).trans (Equiv.Perm.one_apply c).symm)
    have hpx : ¬ p x := fun hp => hx (hfix x hp)
    have hpy : ¬ p (higmanVCOrbit_pi C r x) := fun hp =>
      hx ((higmanVCOrbit_pi C r).injective (hfix _ hp))
    have hlt := Equiv.Perm.card_support_swap_mul hx
    have hpi : higmanVCOrbit_pi C (FreeGroup.of (x, higmanVCOrbit_pi C r x) * r) =
        Equiv.swap x (higmanVCOrbit_pi C r x) * higmanVCOrbit_pi C r := by
      simp only [map_mul, higmanVCOrbit_pi_of]
    have hmem := ih (FreeGroup.of (x, higmanVCOrbit_pi C r x) * r) (by rw [hpi]; omega)
      (fun c hc => by
        rw [hpi, Equiv.Perm.mul_apply, hfix c hc]
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hpx (h ▸ hc)) (fun h => hpy (h ▸ hc)))
    rw [higmanVCOrbit_mk_of_mul] at hmem
    have h2 := K.mul_mem (K.inv_mem (hK x _ hpx hpy)) hmem
    rwa [inv_mul_cancel_left] at h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_mem_of_fix

/-- **Balanced/fixed split.**  If `π r` preserves the length of every leaf with property
`p`, then `ι r = u * σ` with `u ∈ U` and `σ` in every subgroup `K` that contains the
letters between leaves without `p`.  The proof peels `(x, π x)` for a moved `p`-leaf `x`.
That letter is balanced, and the invariant survives the peel. -/
theorem higmanVCOrbit_split {d : ℕ} {C : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (p : ↥C → Prop) {K : Subgroup (higmanVCCommon_Q d)}
    (hK : ∀ x y : ↥C, ¬ p x → ¬ p y →
      higmanVCCommon_mk d (FreeGroup.of (x.1, y.1)) ∈ K) :
    ∀ (k : ℕ) (r : FreeGroup (↥C × ↥C)), (higmanVCOrbit_pi C r).support.card ≤ k →
      (∀ c, p c → (higmanVCOrbit_pi C r c).1.length = c.1.length) →
        ∃ u ∈ higmanVCTreeNF_U d, ∃ σ ∈ K,
          higmanVCCommon_mk d (higmanVCAll_iota C r) = u * σ := by
  intro k
  induction k with
  | zero =>
    intro r hk _
    refine ⟨1, Subgroup.one_mem _, 1, K.one_mem, ?_⟩
    rw [higmanVCOrbit_mk_eq_one hC (Equiv.Perm.card_support_eq_zero.mp (Nat.le_zero.mp hk)),
      one_mul]
  | succ k ih =>
    intro r hk hlen
    by_cases hex : ∃ x, p x ∧ higmanVCOrbit_pi C r x ≠ x
    · obtain ⟨x, hpx, hx⟩ := hex
      have hlt := Equiv.Perm.card_support_swap_mul hx
      have hpi : higmanVCOrbit_pi C (FreeGroup.of (x, higmanVCOrbit_pi C r x) * r) =
          Equiv.swap x (higmanVCOrbit_pi C r x) * higmanVCOrbit_pi C r := by
        simp only [map_mul, higmanVCOrbit_pi_of]
      have hlen' : ∀ c, p c → (higmanVCOrbit_pi C
          (FreeGroup.of (x, higmanVCOrbit_pi C r x) * r) c).1.length = c.1.length := by
        intro c hc
        rw [hpi, Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · rw [hlen x hpx, ← h1, hlen c hc]
        · rw [(higmanVCOrbit_pi C r).injective h2]
        · exact hlen c hc
      obtain ⟨u, hu, σ, hσ, heq⟩ :=
        ih (FreeGroup.of (x, higmanVCOrbit_pi C r x) * r) (by rw [hpi]; omega) hlen'
      have hl : higmanVCCommon_mk d (FreeGroup.of (x.1, (higmanVCOrbit_pi C r x).1)) ∈
          higmanVCTreeNF_U d := higmanVCTreeNF_letter_mem (hlen x hpx).symm
      refine ⟨(higmanVCCommon_mk d (FreeGroup.of (x.1, (higmanVCOrbit_pi C r x).1)))⁻¹ * u,
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hu, σ, hσ, ?_⟩
      rw [mul_assoc, ← heq, higmanVCOrbit_mk_of_mul, inv_mul_cancel_left]
    · have hfix : ∀ c, p c → higmanVCOrbit_pi C r c = c := fun c hc => by
        by_contra hne
        exact hex ⟨c, hc, hne⟩
      exact ⟨1, Subgroup.one_mem _, higmanVCCommon_mk d (higmanVCAll_iota C r),
        higmanVCOrbit_mem_of_fix hC p hK (k + 1) r hk hfix, (one_mul _).symm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbit_split

end GroupApproximation.BooneHigman.Metabelian.Envelope
