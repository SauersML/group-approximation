import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# Step B restricted to words of defect at most one (lane bh-met-77i)

**Proved here, with no hypotheses.**  Modulo `K = normalClosure (higmanVC_rels d fun _ => True)`,
for `1 < d`, every word of the all-swaps free group is congruent to `higmanVCTree_iota d r'`, a
word whose letters `(u, v)` all have `| |u| - |v| | ≤ 1` (`higmanVCTree_mem`,
`higmanVCTree_exists_small`).

**Gap: `HigmanVCTreeDefectStatement`.**  This is `HigmanVCCentralBalancedStatement` (lane
bh-met-77h) restricted to kernel words all of whose letters have defect `≤ 1`.

* **Reduction (proved):** `higmanVCTree_balanced_of_defect`.  Rewrite the kernel word to a
  defect-`≤ 1` word with the same class in `Q`.  The rewritten word is again in the kernel,
  because `K ≤ ker`, and it is again central modulo `K`.
* **It is equivalent to the target as a Prop, NOT strictly weaker**
  (`higmanVCTree_defect_of_ker_le`, using the empty product).  As `EnvelopeHigmanVCAllReduce`
  explains, no gap that yields (1) with nothing else supplied can be strictly weaker.
* **It is strictly smaller in proof content.**  The balanced statement must eliminate unbalanced
  letters of every defect.  The gap only sees letters of defect `0` or `1`.  Elimination of
  defect `≥ 2` is discharged here by the detour relator `(u, v) = (w, v) (u, w) (w, v)`.
* **LOUD: the reduction is modest.**  Defect-`1` letters still generate Thompson-`F`-like
  elements.  The single-antichain counterexample of lane bh-met-77h, the letters `(0, 1)` and
  `(00, 1)`, already has defect `≤ 1`.  So the cross-code normal-form (tree-pair) argument is
  still entirely inside the gap.  This lane did not supply it.
* **Truth.**  The gap is true if and only if (1) is true.  (1) is the standard presentation of
  `V_d`; it is believed but not verified here.  `scratchpad/bh-met-77i/check.py` checks the
  proved part (the intermediate word and the detour identity, as permutations, `d = 2, 3`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Every letter lies in `higmanVCTree_S d`, by induction on the defect bound `n + 1`. -/
theorem higmanVCTree_letter_mem_aux {d : ℕ} (hd : 1 < d) (n : ℕ) :
    ∀ u v : List (Fin d), u.length ≤ v.length + n + 1 → v.length ≤ u.length + n + 1 →
      higmanVCCommon_mk d (FreeGroup.of (u, v)) ∈ higmanVCTree_S d := by
  induction n with
  | zero =>
    intro u v h1 h2
    exact higmanVCTree_small_mem (by omega) (by omega)
  | succ n ih =>
    intro u v h1 h2
    by_cases hc : ¬ u <+: v ∧ ¬ v <+: u
    · by_cases h3 : v.length ≤ u.length + n + 1
      · by_cases h4 : u.length ≤ v.length + n + 1
        · exact ih u v h4 h3
        · rw [higmanVCTree_mk_swap hc.1 hc.2]
          exact higmanVCTree_step hd ih hc.2 hc.1 (by omega) (by omega)
      · exact higmanVCTree_step hd ih hc.1 hc.2 (by omega) (by omega)
    · rw [higmanVCCommon_mk_comparable hc]
      exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_letter_mem_aux

/-- **Defect reduction for letters.** -/
theorem higmanVCTree_letter_mem {d : ℕ} (hd : 1 < d) (u v : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (u, v)) ∈ higmanVCTree_S d :=
  higmanVCTree_letter_mem_aux hd (u.length + v.length) u v (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_letter_mem

/-- **Defect reduction for words.**  Modulo the relators every word is a word in letters of
defect at most one. -/
theorem higmanVCTree_mem {d : ℕ} (hd : 1 < d) (g : FreeGroup (List (Fin d) × List (Fin d))) :
    higmanVCCommon_mk d g ∈ higmanVCTree_S d := by
  induction g using FreeGroup.induction_on with
  | C1 =>
    rw [map_one]
    exact Subgroup.one_mem _
  | of p =>
    obtain ⟨u, v⟩ := p
    exact higmanVCTree_letter_mem hd u v
  | inv_of p _ =>
    obtain ⟨u, v⟩ := p
    rw [map_inv]
    exact Subgroup.inv_mem _ (higmanVCTree_letter_mem hd u v)
  | mul g₁ g₂ ih₁ ih₂ =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ih₁ ih₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_mem

/-- The defect reduction, as an explicit word. -/
theorem higmanVCTree_exists_small {d : ℕ} (hd : 1 < d)
    (g : FreeGroup (List (Fin d) × List (Fin d))) :
    ∃ r : FreeGroup (higmanVCTree_Small d),
      higmanVCCommon_mk d (higmanVCTree_iota d r) = higmanVCCommon_mk d g := by
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (higmanVCTree_mem hd g)
  exact ⟨r, hr⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTree_exists_small

end GroupApproximation.BooneHigman.Metabelian.Envelope
