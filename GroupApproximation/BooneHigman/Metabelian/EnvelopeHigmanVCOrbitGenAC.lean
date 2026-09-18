import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenConj
import GroupApproximation.Meta.AxiomGuard

/-!
# The atom antichain (lane bh-met-91l)

For a letter `x : Fin d` put
* `TA x = {x i | i} ∪ {j | j ≠ x}` (the tree `{[]}` expanded at `[]`, then at `[x]`);
* `TB x = {x x i | i} ∪ {x j | j ≠ x} ∪ {j | j ≠ x}` (`TA x` expanded at `[x, x]`);
* `C a b x = a · TA x ∪ b · TB x`.

For incomparable `a, b` the set `C a b x` is a prefix antichain (`higmanVCOrbitGen_C_isAC`).
It contains every leaf that the splits of `m(a₁, b₂)`, `m(a₁, b₁)` and `t = m(a, b)` use,
except the leaves `a₂, b₂` of `m(a₂, b₂)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `TA x`: `{[]}` expanded at `[]`, then at `[x]`. -/
abbrev higmanVCOrbitGen_TA {d : ℕ} (x : Fin d) : Finset (List (Fin d)) :=
  higmanVCLeafExp_expand (higmanVCLeafExp_expand ({[]} : Finset (List (Fin d))) []) ([] ++ [x])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_TA

/-- `TB x`: `TA x` expanded at `[x, x]`. -/
abbrev higmanVCOrbitGen_TB {d : ℕ} (x : Fin d) : Finset (List (Fin d)) :=
  higmanVCLeafExp_expand (higmanVCOrbitGen_TA x) ([] ++ [x] ++ [x])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_TB

theorem higmanVCOrbitGen_TA_tree {d : ℕ} (x : Fin d) :
    higmanVCLeafExp_IsTree (higmanVCOrbitGen_TA x) :=
  higmanVCLeafExp_IsTree.expand
    (higmanVCLeafExp_IsTree.expand higmanVCLeafExp_IsTree.root (Finset.mem_singleton_self _))
    (higmanVCLeafExp_child_mem _ [] x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_TA_tree

theorem higmanVCOrbitGen_TB_tree {d : ℕ} (x : Fin d) :
    higmanVCLeafExp_IsTree (higmanVCOrbitGen_TB x) :=
  higmanVCLeafExp_IsTree.expand (higmanVCOrbitGen_TA_tree x)
    (higmanVCLeafExp_child_mem _ ([] ++ [x]) x)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_TB_tree

/-- The atom antichain `C a b x = a · TA x ∪ b · TB x`. -/
def higmanVCOrbitGen_C {d : ℕ} (a b : List (Fin d)) (x : Fin d) : Finset (List (Fin d)) :=
  (higmanVCOrbitGen_TA x).image (a ++ ·) ∪ (higmanVCOrbitGen_TB x).image (b ++ ·)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_C

/-- The atom antichain is a prefix antichain. -/
theorem higmanVCOrbitGen_C_isAC {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (x : Fin d) : higmanVCTreeNFWitPivot_IsAC (higmanVCOrbitGen_C a b x) := by
  have hA := higmanVCLeafExp_tree_isAC (higmanVCOrbitGen_TA_tree x)
  have hB := higmanVCLeafExp_tree_isAC (higmanVCOrbitGen_TB_tree x)
  intro u hu v hv huv hpre
  simp only [higmanVCOrbitGen_C, Finset.mem_union, Finset.mem_image] at hu hv
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hv with ⟨e', he', rfl⟩ | ⟨e', -, rfl⟩
    · exact hA e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj a).mp hpre)
    · exact higmanVCOrbitGap_incomp_append hab hba e e' hpre
  · rcases hv with ⟨e', -, rfl⟩ | ⟨e', he', rfl⟩
    · exact higmanVCOrbitGap_incomp_append hba hab e e' hpre
    · exact hB e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj b).mp hpre)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_C_isAC

theorem higmanVCOrbitGen_mem_C_a {d : ℕ} {a b : List (Fin d)} {x : Fin d} {e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitGen_TA x) (hu : a ++ e = u) : u ∈ higmanVCOrbitGen_C a b x := by
  rw [higmanVCOrbitGen_C]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_mem_C_a

theorem higmanVCOrbitGen_mem_C_b {d : ℕ} {a b : List (Fin d)} {x : Fin d} {e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitGen_TB x) (hu : b ++ e = u) : u ∈ higmanVCOrbitGen_C a b x := by
  rw [higmanVCOrbitGen_C]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_mem_C_b

