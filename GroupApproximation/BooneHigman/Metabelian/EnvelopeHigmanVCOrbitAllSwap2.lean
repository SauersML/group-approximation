import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllFam
import GroupApproximation.Meta.AxiomGuard

/-!
# Every length-difference-two single swap passes the pivot (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitAllFam`, with `|b| = |a| + 1`.  Write a single swap as
`m(a e, b e')`, and put `k = |e'| - |e|`.  The swaps with `e, e'` incomparable or equal are
symmetric, and `k = ∓1` are balanced or twist-balanced, so all of these are mixed.  The
non-mixed single swaps are the ones with `e, e'` comparable, distinct and `|k| ≥ 2`.

* `higmanVCOrbitAll_fam_of_swap2`: `m(a e, b e y z)` lies in the path-atom class for **all**
  letters `y, z`.  For `z ≠ y`, conjugate the path atom `m(a e, b e y y)` by the balanced letter
  `u = m(b e y y, b e y z)`, and note `u = t v t⁻¹` with `v = m(a e y y, a e y z)` balanced.
* `higmanVCOrbitAll_famCls_of_swap2'`: `m(a e y z, b e)` (`k = -2`) is the twist of such a
  swap.
* `higmanVCOrbitAll_swap2_mem_S`, `higmanVCOrbitAll_swap2'_mem_S`: so every single swap
  with `|k| = 2` passes the pivot.  The single swaps still open have `|k| ≥ 3`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `m(a e, b e y z)` lies in the path-atom class. -/
theorem higmanVCOrbitAll_fam_of_swap2 {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (e : List (Fin d)) (y z : Fin d) :
    higmanVCOrbitAll_Fam d a b
      (higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e ++ [y] ++ [z]))) := by
  by_cases hz : z = y
  · rw [hz]
    exact ⟨1, (higmanVCTreeNF_U d).one_mem, e, y, 1, (higmanVCTreeNF_U d).one_mem,
      by simp only [one_mul, mul_one, mul_inv_cancel]⟩
  have pa : a <+: a ++ e := List.prefix_append a e
  have pb1 : b <+: b ++ e ++ [y] := (List.prefix_append b e).trans (List.prefix_append _ [y])
  have pb2 : b <+: b ++ e ++ [y] ++ [y] := pb1.trans (List.prefix_append _ [y])
  have pbz : b <+: b ++ e ++ [y] ++ [z] := pb1.trans (List.prefix_append _ [z])
  have n1 : ¬ b ++ e ++ [y] ++ [y] <+: b ++ e ++ [y] ++ [z] :=
    higmanVCOrbitAll_ne_prefix (Ne.symm hz) (b ++ e ++ [y])
  have n2 : ¬ b ++ e ++ [y] ++ [z] <+: b ++ e ++ [y] ++ [y] :=
    higmanVCOrbitAll_ne_prefix hz (b ++ e ++ [y])
  have m1 : ¬ a ++ e ++ [y] ++ [y] <+: a ++ e ++ [y] ++ [z] :=
    higmanVCOrbitAll_ne_prefix (Ne.symm hz) (a ++ e ++ [y])
  have m2 : ¬ a ++ e ++ [y] ++ [z] <+: a ++ e ++ [y] ++ [y] :=
    higmanVCOrbitAll_ne_prefix hz (a ++ e ++ [y])
  have x1 := higmanVCOrbitGen_incomp hab hba pa pb2
  have x2 := higmanVCOrbitGen_incomp hba hab pb2 pa
  have x3 := higmanVCOrbitGen_incomp hab hba pa pbz
  have x4 := higmanVCOrbitGen_incomp hba hab pbz pa
  have E1 := higmanVCOrbitGen_conj n1 n2 (vgen_mapsCone_coneSwap_fix n1 n2 x1 x2 x3 x4)
    (mapsCone_coneSwap_left n1 n2) x1 x2 x3 x4
  have mL := mapsCone_coneSwap_left hab hba
  have E2 := higmanVCOrbitGen_conj hab hba (((mL.append e).append [y]).append [y])
    (((mL.append e).append [y]).append [z]) m1 m2 n1 n2
  have hu : higmanVCCommon_mk d (FreeGroup.of (b ++ e ++ [y] ++ [y], b ++ e ++ [y] ++ [z])) ∈
      higmanVCTreeNF_U d :=
    higmanVCTreeNF_letter_mem (by simp only [List.length_append, List.length_singleton])
  have hv : higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [y], a ++ e ++ [y] ++ [z])) ∈
      higmanVCTreeNF_U d :=
    higmanVCTreeNF_letter_mem (by simp only [List.length_append, List.length_singleton])
  refine ⟨_, hu, e, y, _, hv, ?_⟩
  rw [E2, ← E1, inv_eq_of_mul_eq_one_right
    (higmanVCCommon_mk_sq (b ++ e ++ [y] ++ [y]) (b ++ e ++ [y] ++ [z]))]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_fam_of_swap2

/-- `m(a e y z, b e)` lies in the twisted path-atom class. -/
theorem higmanVCOrbitAll_famCls_of_swap2' {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (e : List (Fin d)) (y z : Fin d) :
    higmanVCOrbitAll_FamCls d a b
      (higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [z], b ++ e))) := by
  refine Or.inr ?_
  have pa' : a <+: a ++ e := List.prefix_append a e
  have pa : a <+: a ++ e ++ [y] ++ [z] :=
    (pa'.trans (List.prefix_append _ [y])).trans (List.prefix_append _ [z])
  have pb : b <+: b ++ e := List.prefix_append b e
  have pbz : b <+: b ++ e ++ [y] ++ [z] :=
    (pb.trans (List.prefix_append _ [y])).trans (List.prefix_append _ [z])
  have mL := mapsCone_coneSwap_left hab hba
  have mR := mapsCone_coneSwap_right hab hba
  have E := higmanVCOrbitGen_conj hab hba (((mL.append e).append [y]).append [z])
    (mR.append e) (higmanVCOrbitGen_incomp hab hba pa pb) (higmanVCOrbitGen_incomp hba hab pb pa)
    (higmanVCOrbitGen_incomp hba hab pbz pa') (higmanVCOrbitGen_incomp hab hba pa' pbz)
  have ht : (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a, b)) :=
    inv_eq_of_mul_eq_one_right (higmanVCCommon_mk_sq a b)
  have hh : (higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [z], b ++ e)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [z], b ++ e)) :=
    inv_eq_of_mul_eq_one_right (higmanVCCommon_mk_sq (a ++ e ++ [y] ++ [z]) (b ++ e))
  have e2 : (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ *
      (higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [z], b ++ e)))⁻¹ *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e ++ [y] ++ [z])) := by
    rw [hh, ht]
    rw [ht] at E
    rw [E]
    exact higmanVCOrbitGen_symm (higmanVCOrbitGen_incomp hab hba pa' pbz)
      (higmanVCOrbitGen_incomp hba hab pbz pa')
  rw [e2]
  exact higmanVCOrbitAll_fam_of_swap2 hab hba e y z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_famCls_of_swap2'

/-- Every single swap `m(a e, b e y z)` (`k = 2`) passes the pivot. -/
theorem higmanVCOrbitAll_swap2_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (e : List (Fin d)) (y z : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ e, b ++ e ++ [y] ++ [z])) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCOrbitAll_fam_class_mem_S hab hba hlen (higmanVCOrbitAll_fam_of_swap2 hab hba e y z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_swap2_mem_S

/-- Every single swap `m(a e y z, b e)` (`k = -2`) passes the pivot. -/
theorem higmanVCOrbitAll_swap2'_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (hlen : b.length = a.length + 1) (e : List (Fin d)) (y z : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ e ++ [y] ++ [z], b ++ e)) *
      higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d :=
  higmanVCOrbitAll_famCls_mem_S hab hba hlen (higmanVCOrbitAll_famCls_of_swap2' hab hba e y z)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_swap2'_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
