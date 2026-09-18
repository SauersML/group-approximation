import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllPathMem
import GroupApproximation.Meta.AxiomGuard

/-!
# The path-atom identity and its pieces (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitGenConj`, `t = m(a, b)`.  For a word `p` and a letter
`y`, write `a₁ = a p`, `a₂ = a p y`, `a₃ = a p y y` (similarly for `b`), and let
`CP = higmanVCOrbitAll_CP a b p y`.  The same four conjugation relations as for the atom
(`higmanVCOrbitGen_atom_eq`) give the **path-atom identity**
`m(a₁, b₃) · t = m(a₁, b₂)⁻¹ · (m(a₂, b₂)⁻¹ · t) · m(b₁, a₂)`
(`higmanVCOrbitAll_fam_eq`).  Then
* `higmanVCOrbitAll_L_mem`: `m(a₁, b₂) ∈ H_CP`, split over the leaves `a p i` and `b p y i`;
* `higmanVCOrbitAll_PtP_mem`: `m(a₂, b₂)⁻¹ · t ∈ H_CP`, by `higmanVCOrbitAll_path_mem`
  along the path `p y`.

For `p = [x]`, `y = x` this is the atom identity.  The identity and both memberships were
checked on permutations of words in `V_d` (`d ∈ {2, 3}`, several pivots, all short `p`,
all `y`) by `scratchpad/bh-met-91x/check_ids.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The path-atom identity.**
`m(a p, b p y y) t = m(a p, b p y)⁻¹ (m(a p y, b p y)⁻¹ t) m(b p, a p y)`. -/
theorem higmanVCOrbitAll_fam_eq {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (p : List (Fin d)) (y : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y] ++ [y])) *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) =
      (higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y])))⁻¹ *
        ((higmanVCCommon_mk d (FreeGroup.of (a ++ p ++ [y], b ++ p ++ [y])))⁻¹ *
          higmanVCCommon_mk d (FreeGroup.of (a, b))) *
        higmanVCCommon_mk d (FreeGroup.of (b ++ p, a ++ p ++ [y])) := by
  have pa1 : a <+: a ++ p := List.prefix_append a p
  have pa2 : a <+: a ++ p ++ [y] := pa1.trans (List.prefix_append _ [y])
  have pa3 : a <+: a ++ p ++ [y] ++ [y] := pa2.trans (List.prefix_append _ [y])
  have pb1 : b <+: b ++ p := List.prefix_append b p
  have pb2 : b <+: b ++ p ++ [y] := pb1.trans (List.prefix_append _ [y])
  have pb3 : b <+: b ++ p ++ [y] ++ [y] := pb2.trans (List.prefix_append _ [y])
  have mL := mapsCone_coneSwap_left hab hba
  have mR := mapsCone_coneSwap_right hab hba
  have i12 := higmanVCOrbitGen_incomp hba hab pb1 pa2
  have i21 := higmanVCOrbitGen_incomp hab hba pa2 pb1
  have i13 := higmanVCOrbitGen_incomp hba hab pb1 pa3
  have i31 := higmanVCOrbitGen_incomp hab hba pa3 pb1
  have j13 := higmanVCOrbitGen_incomp hab hba pa1 pb3
  have j31 := higmanVCOrbitGen_incomp hba hab pb3 pa1
  have j12 := higmanVCOrbitGen_incomp hab hba pa1 pb2
  have j21 := higmanVCOrbitGen_incomp hba hab pb2 pa1
  have j22 := higmanVCOrbitGen_incomp hab hba pa2 pb2
  have k22 := higmanVCOrbitGen_incomp hba hab pb2 pa2
  refine higmanVCOrbitGen_key_eq
    (k := higmanVCCommon_mk d (FreeGroup.of (b ++ p, a ++ p ++ [y] ++ [y]))) ?_ ?_ ?_ ?_
  · exact higmanVCOrbitGen_conj hab hba (mR.append p)
      (((mL.append p).append [y]).append [y]) i13 i31 j13 j31
  · exact higmanVCOrbitGen_conj i12 i21 (mapsCone_coneSwap_left i12 i21)
      ((mapsCone_coneSwap_right i12 i21).append [y]) i13 i31 j22 k22
  · exact higmanVCOrbitGen_conj hab hba (mR.append p) ((mL.append p).append [y]) i12 i21
      j12 j21
  · exact (higmanVCOrbitGen_conj hab hba ((mL.append p).append [y])
      ((mR.append p).append [y]) j22 k22 k22 j22).trans ((higmanVCOrbitGen_symm j22 k22).trans
        (inv_eq_of_mul_eq_one_right
          (higmanVCCommon_mk_sq (a ++ p ++ [y]) (b ++ p ++ [y]))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_fam_eq

theorem higmanVCOrbitAll_mem_CP_a {d : ℕ} {a b p e u : List (Fin d)} {y : Fin d}
    (he : e ∈ higmanVCOrbitAll_pathSet p) (hu : a ++ e = u) :
    u ∈ higmanVCOrbitAll_CP a b p y := by
  rw [higmanVCOrbitAll_CP]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_mem_CP_a

theorem higmanVCOrbitAll_mem_CP_b {d : ℕ} {a b p e u : List (Fin d)} {y : Fin d}
    (he : e ∈ higmanVCOrbitAll_pathSet (p ++ [y])) (hu : b ++ e = u) :
    u ∈ higmanVCOrbitAll_CP a b p y := by
  rw [higmanVCOrbitAll_CP]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_mem_CP_b

/-- `m(a p, b p y) ∈ H_CP`. -/
theorem higmanVCOrbitAll_L_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (p : List (Fin d)) (y : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p ++ [y])) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitAll_CP a b p y) := by
  have pa1 : a <+: a ++ p := List.prefix_append a p
  have pb2 : b <+: b ++ p ++ [y] := (List.prefix_append b p).trans (List.prefix_append _ [y])
  rw [higmanVCCommon_mk_split (higmanVCOrbitGen_incomp hab hba pa1 pb2)
    (higmanVCOrbitGen_incomp hba hab pb2 pa1), higmanVC_splitAll]
  exact higmanVCOrbitGen_split_mem (a ++ p) (b ++ p ++ [y]) (List.finRange d) fun i _ =>
    higmanVCLeafExp_letter_mem_H (higmanVCOrbitAll_mem_CP_a (higmanVCOrbitAll_mem_child p i)
      (by simp)) (higmanVCOrbitAll_mem_CP_b (higmanVCOrbitAll_mem_child (p ++ [y]) i) (by simp))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_L_mem

/-- `m(a p y, b p y)⁻¹ · t ∈ H_CP`. -/
theorem higmanVCOrbitAll_PtP_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (p : List (Fin d)) (y : Fin d) :
    (higmanVCCommon_mk d (FreeGroup.of (a ++ p ++ [y], b ++ p ++ [y])))⁻¹ *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitAll_CP a b p y) := by
  have hK : ∀ (q : List (Fin d)) (y' j : Fin d), q ++ [y'] <+: p ++ [y] → j ≠ y' →
      higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [j], b ++ q ++ [j])) ∈
        higmanVCTreeNFWitPivot_H d (higmanVCOrbitAll_CP a b p y) := by
    intro q y' j hq hj
    have hA : a ++ q ++ [j] ∈ higmanVCOrbitAll_CP a b p y := by
      rcases higmanVCOrbitAll_prefix_snoc hq with h | ⟨hqp, -⟩
      · exact higmanVCOrbitAll_mem_CP_a (higmanVCOrbitAll_mem_sib p q y' j h hj) (by simp)
      · exact higmanVCOrbitAll_mem_CP_a (higmanVCOrbitAll_mem_child p j) (by simp [hqp])
    have hB : b ++ q ++ [j] ∈ higmanVCOrbitAll_CP a b p y :=
      higmanVCOrbitAll_mem_CP_b (higmanVCOrbitAll_mem_sib (p ++ [y]) q y' j hq hj) (by simp)
    exact higmanVCLeafExp_letter_mem_H hA hB
  simpa only [List.append_assoc] using higmanVCOrbitAll_path_mem (p ++ [y]) a b hab hba hK

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_PtP_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
