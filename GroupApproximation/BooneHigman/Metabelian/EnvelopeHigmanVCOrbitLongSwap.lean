import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitLongPath
import GroupApproximation.Meta.AxiomGuard

/-!
# Long single swaps with a nonempty common stem pass the pivot (lane bh-met-92d)

Notation as in `EnvelopeHigmanVCOrbitLongPath`.  For letters `j ≠ y`, put
`x = m(a q y, a q j) ∈ U`.  Then `t x t⁻¹ = m(b q y, b q j) ∈ U`, and conjugation by `x`
turns `m(a q j, b q y r i)` into `m(a q y, b q y r i)`.  With `P = q y r`, `q j` is a sibling
and `q y r i` is a child along `P`, so `m(a q j, b q y r i) · t ∈ H_D ⊆ S`
(`higmanVCOrbitLong_path_mem_S`).  `N`-conjugation (`higmanVCOrbitLong_conj_mem_S`) then gives
* `higmanVCOrbitLong_swap_mem_S`: `m(a q y, b q y r i) · t ∈ S` for **every** `q`, `r`;
* `higmanVCOrbitLong_swap'_mem_S`: the twisted swap `m(a q y r i, b q y) · t ∈ S`;
* `higmanVCOrbitLong_prefix_mem_S`, `higmanVCOrbitLong_prefix'_mem_S`: `m(a e, b e s) · t` and
  `m(a e s, b e) · t` lie in `S` whenever `e ≠ []` and `s ≠ []`.
So every comparable single swap `m(a e, b e')` with `e ≠ e'` both nonempty passes the pivot,
for every `k = |e'| - |e|`.  No length hypothesis on `a, b` is used.  Checked on permutations
in `V_d` (`d ∈ {2, 3}`, three pivots, 954 cases) by `scratchpad/bh-met-92d/check_long.py`.

LOUD, still open: the swaps with an empty stem, `m(a, b e')` and `m(a e, b)` with
`|e'|, |e| ≥ 3` (`|k| ≤ 2` is `EnvelopeHigmanVCOrbitAllSwap2`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Long swap.**  `m(a q y, b q y r i) · t ∈ S` whenever some letter `j ≠ y` exists. -/
theorem higmanVCOrbitLong_swap_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (q r : List (Fin d)) {y j : Fin d} (hj : j ≠ y) (i : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y], b ++ q ++ [y] ++ r ++ [i])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have pa1 : a <+: a ++ q ++ [y] := (List.prefix_append a q).trans (List.prefix_append _ [y])
  have pa2 : a <+: a ++ q ++ [j] := (List.prefix_append a q).trans (List.prefix_append _ [j])
  have pb : b <+: b ++ q ++ [y] ++ r ++ [i] :=
    (((List.prefix_append b q).trans (List.prefix_append _ [y])).trans
      (List.prefix_append _ r)).trans (List.prefix_append _ [i])
  have n1 : ¬ a ++ q ++ [y] <+: a ++ q ++ [j] := higmanVCOrbitAll_ne_prefix (Ne.symm hj) (a ++ q)
  have n2 : ¬ a ++ q ++ [j] <+: a ++ q ++ [y] := higmanVCOrbitAll_ne_prefix hj (a ++ q)
  have x1 := higmanVCOrbitGen_incomp hba hab pb pa1
  have x2 := higmanVCOrbitGen_incomp hab hba pa1 pb
  have x3 := higmanVCOrbitGen_incomp hba hab pb pa2
  have x4 := higmanVCOrbitGen_incomp hab hba pa2 pb
  have E1 := higmanVCOrbitGen_conj n1 n2 (mapsCone_coneSwap_right n1 n2)
    (vgen_mapsCone_coneSwap_fix n1 n2 x1 x2 x3 x4) x4 x3 x2 x1
  have mL := mapsCone_coneSwap_left hab hba
  have E2 := higmanVCOrbitGen_conj hab hba ((mL.append q).append [y])
    ((mL.append q).append [j]) n1 n2 (higmanVCOrbitAll_ne_prefix (Ne.symm hj) (b ++ q))
    (higmanVCOrbitAll_ne_prefix hj (b ++ q))
  have hx : higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y], a ++ q ++ [j])) ∈
      higmanVCTreeNF_U d :=
    higmanVCTreeNF_letter_mem (by simp only [List.length_append, List.length_singleton])
  have htx : higmanVCCommon_mk d (FreeGroup.of (a, b)) *
      higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y], a ++ q ++ [j])) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ ∈ higmanVCTreeNF_U d := by
    rw [E2]
    exact higmanVCTreeNF_letter_mem (by simp only [List.length_append, List.length_singleton])
  have hP : higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [j], b ++ q ++ [y] ++ r ++ [i])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
    have h0 := higmanVCOrbitLong_path_mem_S hab hba
      (higmanVCOrbitAll_mem_sib (q ++ [y] ++ r) q y j (List.prefix_append _ r) hj)
      (higmanVCOrbitAll_mem_child (q ++ [y] ++ r) i)
    simpa only [List.append_assoc] using h0
  have h := higmanVCOrbitLong_conj_mem_S hP hx htx
  rwa [E1] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_swap_mem_S

/-- **Twisted long swap.**  `m(a q y r i, b q y) · t ∈ S` whenever some letter `j ≠ y`
exists: the long swap for the pivot `(b, a)`, with `m(b, a) = m(a, b)`. -/
theorem higmanVCOrbitLong_swap'_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (q r : List (Fin d)) {y j : Fin d} (hj : j ≠ y) (i : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [y] ++ r ++ [i], b ++ q ++ [y])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  have pa : a <+: a ++ q ++ [y] ++ r ++ [i] :=
    (((List.prefix_append a q).trans (List.prefix_append _ [y])).trans
      (List.prefix_append _ r)).trans (List.prefix_append _ [i])
  have pb : b <+: b ++ q ++ [y] := (List.prefix_append b q).trans (List.prefix_append _ [y])
  have h := higmanVCOrbitLong_swap_mem_S hba hab q r hj i
  rwa [higmanVCOrbitGen_symm hab hba, higmanVCOrbitGen_symm
    (higmanVCOrbitGen_incomp hab hba pa pb) (higmanVCOrbitGen_incomp hba hab pb pa)] at h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_swap'_mem_S

/-- **Comparable swaps, nonempty stem.**  `m(a e, b e s) · t ∈ S` for `e ≠ []`, `s ≠ []`. -/
theorem higmanVCOrbitLong_prefix_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hd : 1 < d) {e s : List (Fin d)} (he : e ≠ []) (hs : s ≠ []) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e ++ s)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨q, y, rfl⟩ : ∃ (q : List (Fin d)) (y : Fin d), e = q ++ [y] :=
    ⟨_, _, (List.dropLast_append_getLast he).symm⟩
  obtain ⟨r, i, rfl⟩ : ∃ (r : List (Fin d)) (i : Fin d), s = r ++ [i] :=
    ⟨_, _, (List.dropLast_append_getLast hs).symm⟩
  obtain ⟨j, hj⟩ := exists_ne y
  simpa only [List.append_assoc] using higmanVCOrbitLong_swap_mem_S hab hba q r hj i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_prefix_mem_S

/-- **Comparable swaps, nonempty stem, twisted.**  `m(a e s, b e) · t ∈ S` for `e, s ≠ []`. -/
theorem higmanVCOrbitLong_prefix'_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hd : 1 < d) {e s : List (Fin d)} (he : e ≠ []) (hs : s ≠ []) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ s, b ++ e)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨q, y, rfl⟩ : ∃ (q : List (Fin d)) (y : Fin d), e = q ++ [y] :=
    ⟨_, _, (List.dropLast_append_getLast he).symm⟩
  obtain ⟨r, i, rfl⟩ : ∃ (r : List (Fin d)) (i : Fin d), s = r ++ [i] :=
    ⟨_, _, (List.dropLast_append_getLast hs).symm⟩
  obtain ⟨j, hj⟩ := exists_ne y
  simpa only [List.append_assoc] using higmanVCOrbitLong_swap'_mem_S hab hba q r hj i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitLong_prefix'_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
