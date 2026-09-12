import GroupApproximation.Algebra.InvolutionBlocks

/-!
# Cutting an involution into blocks of bounded size

`Algebra/InvolutionBlocks.lean` shows that an involution with `2k`
transpositions is reachable in two conjugates of `s^{±1}` once `6k ≤ |supp s|`.
An arbitrary involution has too many transpositions for that, so it has to be
cut; this file does the cutting.

The cut is made on the *list* of cycle factors supplied by
`Equiv.Perm.truncCycleFactors`, not on `cycleFactorsFinset`: `List.take` and
`List.drop` split a product with `List.prod_append` and leave no dependent
commutation proof to transport, whereas `Finset.noncommProd` carries its
pairwise-commutation hypothesis in the term and rewriting the underlying finset
drags it along.

## What is proved

* `card_support_eq_two_of_mem` — every cycle factor of an involution is a
  transposition.
* `sq_eq_one_of_cycleType_two` — conversely, a permutation all of whose cycle
  lengths are `2` is an involution; this is what makes each piece of the cut an
  involution again.
* `exists_split` — an involution splits as `w₁ * w₂` with both factors
  involutions and `w₁` carrying exactly the first `j` transpositions.
* `exists_blocks` — hence an involution with `2p` transpositions is a product of
  at most `fuel` involutions whenever `p ≤ fuel * c`, each block carrying at
  most `c` pairs of transpositions.  The induction is on the fuel rather than on
  `p`, which keeps it structural.

Each block has an even number of transpositions by construction — the cut takes
`2c` at a time out of `2p` — which is what
`isBoundedConjProduct_two_of_involution` requires.  What remains for `SO.17` is
the arithmetic that turns `|supp s| ≥ δ|Ω|` into a fuel depending on `δ` alone,
and the parity repair for the case where the two involutions of the target have
oddly many transpositions each.
-/

namespace GroupApproximation
namespace InvolutionBlocks

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Cycle factors of an involution -/

/-- Every cycle factor of an involution is a transposition. -/
theorem card_support_eq_two_of_mem {w : Equiv.Perm Y} (hw : w * w = 1)
    {L : List (Equiv.Perm Y)} (hLprod : L.prod = w)
    (hLcycle : ∀ g ∈ L, g.IsCycle)
    (hLdisj : L.Pairwise Equiv.Perm.Disjoint)
    {g : Equiv.Perm Y} (hg : g ∈ L) : g.support.card = 2 := by
  have hct : w.cycleType = ↑(L.map (Finset.card ∘ Equiv.Perm.support)) :=
    Equiv.Perm.cycleType_eq L hLprod hLcycle hLdisj
  have hall : ∀ b ∈ w.cycleType, b = 2 :=
    Multiset.eq_replicate_card.mp (cycleType_involution hw)
  refine hall _ ?_
  rw [hct]
  exact Multiset.mem_coe.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩)

/-- A permutation all of whose cycle lengths are `2` is an involution: its
order is the least common multiple of its cycle type, which then divides `2`. -/
theorem sq_eq_one_of_cycleType_two {z : Equiv.Perm Y}
    (h : ∀ b ∈ z.cycleType, b = 2) : z * z = 1 := by
  have hlcm : z.cycleType.lcm ∣ 2 := by
    refine Multiset.lcm_dvd.mpr fun b hb => ?_
    simp [h b hb]
  rw [Equiv.Perm.lcm_cycleType] at hlcm
  have hpow := orderOf_dvd_iff_pow_eq_one.mp hlcm
  rwa [pow_two] at hpow

/-! ## The cut -/

/-- **An involution splits into two involutions, the first carrying exactly the
first `j` of its transpositions.**  The cut is `List.take j` / `List.drop j` on
the list of cycle factors. -/
theorem exists_split {w : Equiv.Perm Y} (hw : w * w = 1) (j : ℕ) :
    ∃ w₁ w₂ : Equiv.Perm Y, w₁ * w₂ = w ∧ w₁ * w₁ = 1 ∧ w₂ * w₂ = 1 ∧
      Multiset.card w₁.cycleType = min j (Multiset.card w.cycleType) ∧
      Multiset.card w₂.cycleType = Multiset.card w.cycleType - j := by
  classical
  obtain ⟨L, hLprod, hLcycle, hLdisj⟩ := w.truncCycleFactors.out
  have hlen : L.length = Multiset.card w.cycleType := by
    rw [Equiv.Perm.cycleType_eq L hLprod hLcycle hLdisj, Multiset.coe_card,
      List.length_map]
  have hsub : ∀ M : List (Equiv.Perm Y), M.Sublist L →
      M.prod.cycleType = ↑(M.map (Finset.card ∘ Equiv.Perm.support)) := by
    intro M hM
    exact Equiv.Perm.cycleType_eq M rfl (fun g hg => hLcycle g (hM.subset hg))
      (hLdisj.sublist hM)
  have hall : ∀ M : List (Equiv.Perm Y), M.Sublist L →
      ∀ b ∈ M.prod.cycleType, b = 2 := by
    intro M hM b hb
    rw [hsub M hM] at hb
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp hb)
    exact card_support_eq_two_of_mem hw hLprod hLcycle hLdisj (hM.subset hg)
  have hcard : ∀ M : List (Equiv.Perm Y), M.Sublist L →
      Multiset.card M.prod.cycleType = M.length := by
    intro M hM
    rw [hsub M hM, Multiset.coe_card, List.length_map]
  refine ⟨(L.take j).prod, (L.drop j).prod, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← List.prod_append, List.take_append_drop, hLprod]
  · exact sq_eq_one_of_cycleType_two (hall _ (List.take_sublist j L))
  · exact sq_eq_one_of_cycleType_two (hall _ (List.drop_sublist j L))
  · have h := hcard _ (List.take_sublist j L)
    rw [List.length_take, hlen] at h
    omega
  · have h := hcard _ (List.drop_sublist j L)
    rw [List.length_drop, hlen] at h
    omega

/-! ## Blocks -/

/-- **An involution with `2p` transpositions is a product of at most `fuel`
involutions, each carrying at most `c` pairs of transpositions**, whenever
`p ≤ fuel * c`.

Each block has an *even* number of transpositions, which is what makes it
reachable by `isBoundedConjProduct_two_of_involution`.  The induction is on the
fuel: one block of `2c` transpositions is cut off at each step. -/
theorem exists_blocks (c : ℕ) (_hc : 0 < c) :
    ∀ (fuel p : ℕ), p ≤ fuel * c → ∀ w : Equiv.Perm Y, w * w = 1 →
      Multiset.card w.cycleType = 2 * p →
      ∃ L : List (Equiv.Perm Y), L.prod = w ∧
        (∀ z ∈ L, z * z = 1 ∧
          ∃ k, Multiset.card z.cycleType = 2 * k ∧ k ≤ c) ∧
        L.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hp w hw hcard
      have hp0 : p = 0 := by omega
      have hw1 : w = 1 := by
        refine Equiv.Perm.card_cycleType_eq_zero.mp ?_
        simp [hcard, hp0]
      exact ⟨[], by simp [hw1], by simp, by simp⟩
  | succ fuel ih =>
      intro p hp w hw hcard
      by_cases hpc : p ≤ c
      · refine ⟨[w], by simp, ?_, by simp⟩
        intro z hz
        rw [List.mem_singleton] at hz
        subst hz
        exact ⟨hw, p, hcard, hpc⟩
      · obtain ⟨w₁, w₂, hmul, hw₁, hw₂, hc₁, hc₂⟩ := exists_split hw (2 * c)
        have hc₁' : Multiset.card w₁.cycleType = 2 * c := by
          rw [hc₁, hcard]
          omega
        have hc₂' : Multiset.card w₂.cycleType = 2 * (p - c) := by
          rw [hc₂, hcard]
          omega
        obtain ⟨L₂, hL₂prod, hL₂mem, hL₂len⟩ :=
          ih (p - c) (by
            have : (fuel + 1) * c = fuel * c + c := by ring
            omega) w₂ hw₂ hc₂'
        refine ⟨w₁ :: L₂, ?_, ?_, ?_⟩
        · rw [List.prod_cons, hL₂prod, hmul]
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact ⟨hw₁, c, hc₁', le_rfl⟩
          · exact hL₂mem z hz'
        · rw [List.length_cons]
          omega

end InvolutionBlocks
end GroupApproximation
