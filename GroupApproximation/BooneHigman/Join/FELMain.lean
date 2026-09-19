import GroupApproximation.BooneHigman.Join.FEL

/-!
# The fundamental expansion lemma: the induction (lane bh-pal-met-join)

`fel T σ d`: every element of the antichain subgroup of the leaves of `T` has the expansion
property `FELAt` at every leaf.  See `FEL` for the statement.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

open BTree

theorem jH_induction_mon {d : ℕ} {C : Finset (List (Fin d))} {P : higmanVCCommon_Q d → Prop}
    (h1 : P 1) (hL : ∀ x ∈ C, ∀ y ∈ C, P (jL x y)) (hmul : ∀ a b, P a → P b → P (a * b))
    {σ : higmanVCCommon_Q d} (hσ : σ ∈ jH d C) : P σ := by
  obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hσ
  clear hσ
  induction r using FreeGroup.induction_on with
  | C1 => simpa using h1
  | of p =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    show P (higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of _)))
    rw [higmanVCAll_iota_of]
    exact hL x hx y hy
  | inv_of p _ =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := p
    show P (higmanVCCommon_mk d (higmanVCAll_iota C (FreeGroup.of _)⁻¹))
    rw [map_inv, map_inv, higmanVCAll_iota_of]
    show P (jL x y)⁻¹
    rw [jL_inv]
    exact hL x hx y hy
  | mul a b iha ihb =>
    simp only [MonoidHom.comp_apply, map_mul] at iha ihb ⊢
    exact hmul _ _ iha ihb

#audit_axioms GroupApproximation.BooneHigman.Join.jH_induction_mon

theorem jL_symm {x y : List (Fin 2)} (h1 : ¬ x <+: y) (h2 : ¬ y <+: x) : jL x y = jL y x := by
  have h := jL_conj h1 h2 (mapsCone_coneSwap_left h1 h2) (mapsCone_coneSwap_right h1 h2)
    h1 h2 h2 h1
  rw [jL_inv, jL_sq, one_mul] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Join.jL_symm

/-- Two leaves are equal or incomparable. -/
theorem leaves_eq_or_incomp {T : BTree} {x y : List (Fin 2)} (hx : x ∈ T.leaves)
    (hy : y ∈ T.leaves) : x = y ∨ (¬ x <+: y ∧ ¬ y <+: x) := by
  by_cases h : x = y
  · exact Or.inl h
  · exact Or.inr ⟨leaves_isAC T x hx y hy h, leaves_isAC T y hy x hx (Ne.symm h)⟩

#audit_axioms GroupApproximation.BooneHigman.Join.leaves_eq_or_incomp

theorem mc_jL_right {x y : List (Fin 2)} (h : x = y ∨ (¬ x <+: y ∧ ¬ y <+: x)) :
    MapsCone (jperm 2 (jL x y)) y x := by
  rcases h with rfl | ⟨h1, h2⟩
  · rw [jL_self, jperm_one]
    exact mapsCone_one x
  · rw [jperm_jL h1 h2]
    exact mapsCone_coneSwap_right h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.mc_jL_right

theorem mc_jL_fix {x y z : List (Fin 2)} (h : x = y ∨ (¬ x <+: y ∧ ¬ y <+: x))
    (hxz : ¬ x <+: z) (hzx : ¬ z <+: x) (hyz : ¬ y <+: z) (hzy : ¬ z <+: y) :
    MapsCone (jperm 2 (jL x y)) z z := by
  rcases h with rfl | ⟨h1, h2⟩
  · rw [jL_self, jperm_one]
    exact mapsCone_one z
  · rw [jperm_jL h1 h2]
    exact mapsCone_coneSwap_fix h1 h2 hxz hzx hyz hzy

#audit_axioms GroupApproximation.BooneHigman.Join.mc_jL_fix

theorem fixes_mapsCone {f : Equiv.Perm (Cantor (Fin 2))} {p q c : List (Fin 2)}
    (hfix : Fixes f p q) (h1 : ¬ p <+: c) (h2 : ¬ c <+: p) (h3 : ¬ q <+: c) (h4 : ¬ c <+: q) :
    MapsCone f c c := fun y =>
  hfix _ (fun h => Set.disjoint_left.mp (disjoint_cone h1 h2) h (prepend_mem_cone c y))
    (fun h => Set.disjoint_left.mp (disjoint_cone h3 h4) h (prepend_mem_cone c y))

#audit_axioms GroupApproximation.BooneHigman.Join.fixes_mapsCone

/-- The crossing leaves of `node l r`. -/
abbrev crossP (l : BTree) : List (Fin 2) := 0 :: List.replicate l.rdepth 1

/-- The crossing leaves of `node l r`. -/
abbrev crossQ (r : BTree) : List (Fin 2) := 1 :: List.replicate r.ldepth 0

theorem crossP_mem (l r : BTree) : crossP l ∈ (node l r).leaves :=
  mem_leaves_node.mpr (Or.inl ⟨_, rightmost_mem l, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Join.crossP_mem

theorem crossQ_mem (l r : BTree) : crossQ r ∈ (node l r).leaves :=
  mem_leaves_node.mpr (Or.inr ⟨_, leftmost_mem r, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Join.crossQ_mem

theorem cross_ne (l r : BTree) : crossP l ≠ crossQ r := fun e =>
  absurd (List.cons.inj e).1 (by decide)

#audit_axioms GroupApproximation.BooneHigman.Join.cross_ne

/-- The expansion property of the crossing letter at the right crossing leaf. -/
theorem felAt_cross_right (l r : BTree) :
    FELAt (node l r) (jL (crossP l) (crossQ r)) (crossQ r) := by
  have hp : (crossP l) ∈ (node l r).leaves := crossP_mem l r
  have hq : (crossQ r) ∈ (node l r).leaves := crossQ_mem l r
  have hpq : (crossP l) ≠ (crossQ r) := cross_ne l r
  obtain ⟨f, hf, ρ, hρ, e, m1, m2, m3, hfix⟩ := baseR_adj l.rdepth r.ldepth
  refine ⟨(crossP l), hp, f, hf, ρ, jH_mono ?_ hρ, e, ?_⟩
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rw [mem_lset_expand hq]
    rcases hc with rfl | rfl | rfl
    · exact Or.inl ⟨hp, hpq⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro c' hc'
    rcases (mem_leaves_expand (node l r) hp c').mp hc' with ⟨hc1, hc2⟩ | rfl | rfl
    · by_cases hcq : c' = (crossQ r)
      · subst hcq
        exact ⟨(crossQ r) ++ [1], (mem_leaves_expand (node l r) hq _).mpr (Or.inr (Or.inr rfl)), m3⟩
      · refine ⟨c', (mem_leaves_expand (node l r) hq _).mpr (Or.inl ⟨hc1, hcq⟩), ?_⟩
        exact fixes_mapsCone hfix (leaves_isAC (node l r) (crossP l) hp c' hc1 (Ne.symm hc2))
          (leaves_isAC (node l r) c' hc1 (crossP l) hp hc2) (leaves_isAC (node l r) (crossQ r) hq c' hc1 (Ne.symm hcq))
          (leaves_isAC (node l r) c' hc1 (crossQ r) hq hcq)
    · exact ⟨(crossP l), (mem_leaves_expand (node l r) hq _).mpr (Or.inl ⟨hp, hpq⟩), m1⟩
    · exact ⟨(crossQ r) ++ [0], (mem_leaves_expand (node l r) hq _).mpr (Or.inr (Or.inl rfl)), m2⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_cross_right

/-- The expansion property of the crossing letter at the left crossing leaf. -/
theorem felAt_cross_left (l r : BTree) :
    FELAt (node l r) (jL (crossP l) (crossQ r)) (crossP l) := by
  have hp : (crossP l) ∈ (node l r).leaves := crossP_mem l r
  have hq : (crossQ r) ∈ (node l r).leaves := crossQ_mem l r
  have hpq : (crossP l) ≠ (crossQ r) := cross_ne l r
  have hpq1 : ¬ (crossP l) <+: (crossQ r) := leaves_isAC (node l r) (crossP l) hp (crossQ r) hq hpq
  have hpq2 : ¬ (crossQ r) <+: (crossP l) := leaves_isAC (node l r) (crossQ r) hq (crossP l) hp (Ne.symm hpq)
  obtain ⟨f, hf, ρ, hρ, e, m1, m2, m3, hfix⟩ :=
    baseL_of_baseR hpq1 hpq2 (baseR_adj l.rdepth r.ldepth)
  refine ⟨(crossQ r), hq, f, hf, ρ, jH_mono ?_ hρ, e, ?_⟩
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rw [mem_lset_expand hp]
    rcases hc with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨hq, Ne.symm hpq⟩
  · intro c' hc'
    rcases (mem_leaves_expand (node l r) hq c').mp hc' with ⟨hc1, hc2⟩ | rfl | rfl
    · by_cases hcp : c' = (crossP l)
      · subst hcp
        exact ⟨(crossP l) ++ [0], (mem_leaves_expand (node l r) hp _).mpr (Or.inr (Or.inl rfl)), m1⟩
      · refine ⟨c', (mem_leaves_expand (node l r) hp _).mpr (Or.inl ⟨hc1, hcp⟩), ?_⟩
        exact fixes_mapsCone hfix (leaves_isAC (node l r) (crossP l) hp c' hc1 (Ne.symm hcp))
          (leaves_isAC (node l r) c' hc1 (crossP l) hp hcp) (leaves_isAC (node l r) (crossQ r) hq c' hc1 (Ne.symm hc2))
          (leaves_isAC (node l r) c' hc1 (crossQ r) hq hc2)
    · exact ⟨(crossP l) ++ [1], (mem_leaves_expand (node l r) hp _).mpr (Or.inr (Or.inr rfl)), m2⟩
    · exact ⟨(crossQ r), (mem_leaves_expand (node l r) hp _).mpr (Or.inl ⟨hq, Ne.symm hpq⟩), m3⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_cross_left

/-- The crossing letter has the expansion property at every leaf. -/
theorem felAt_cross (l r : BTree) {e : List (Fin 2)} (he : e ∈ (node l r).leaves) :
    FELAt (node l r) (jL (crossP l) (crossQ r)) e := by
  by_cases hp : e = crossP l
  · rw [hp]
    exact felAt_cross_left l r
  by_cases hq : e = crossQ r
  · rw [hq]
    exact felAt_cross_right l r
  refine felAt_of_mem he (jL_mem_jH ?_ ?_)
  · rw [mem_lset_expand he]
    exact Or.inl ⟨crossP_mem l r, fun h => hp h.symm⟩
  · rw [mem_lset_expand he]
    exact Or.inl ⟨crossQ_mem l r, fun h => hq h.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_cross

/-- The left letters of `node l r`. -/
theorem felAt_left_letter {l r : BTree} (ihl : ∀ σ ∈ jH 2 l.lset, ∀ d ∈ l.leaves, FELAt l σ d)
    {u v : List (Fin 2)} (hu : u ∈ l.leaves) (hv : v ∈ l.leaves) {e : List (Fin 2)}
    (he : e ∈ (node l r).leaves) : FELAt (node l r) (jL (0 :: u) (0 :: v)) e := by
  have hlet : jL (0 :: u) (0 :: v) = jPhi 2 [0] (jL u v) := (jPhi_jL [0] u v).symm
  rcases mem_leaves_node.mp he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
  · rw [hlet]
    exact felAt_phi_zero (ihl _ (jL_mem_jH (mem_lset.mpr hu) (mem_lset.mpr hv)) e' he')
  · refine felAt_of_mem he (jL_mem_jH ?_ ?_)
    · rw [expand_node_one, mem_lset, mem_leaves_node]
      exact Or.inl ⟨u, hu, rfl⟩
    · rw [expand_node_one, mem_lset, mem_leaves_node]
      exact Or.inl ⟨v, hv, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_left_letter

/-- The right letters of `node l r`. -/
theorem felAt_right_letter {l r : BTree} (ihr : ∀ σ ∈ jH 2 r.lset, ∀ d ∈ r.leaves, FELAt r σ d)
    {u v : List (Fin 2)} (hu : u ∈ r.leaves) (hv : v ∈ r.leaves) {e : List (Fin 2)}
    (he : e ∈ (node l r).leaves) : FELAt (node l r) (jL (1 :: u) (1 :: v)) e := by
  have hlet : jL (1 :: u) (1 :: v) = jPhi 2 [1] (jL u v) := (jPhi_jL [1] u v).symm
  rcases mem_leaves_node.mp he with ⟨e', he', rfl⟩ | ⟨e', he', rfl⟩
  · refine felAt_of_mem he (jL_mem_jH ?_ ?_)
    · rw [expand_node_zero, mem_lset, mem_leaves_node]
      exact Or.inr ⟨u, hu, rfl⟩
    · rw [expand_node_zero, mem_lset, mem_leaves_node]
      exact Or.inr ⟨v, hv, rfl⟩
  · rw [hlet]
    exact felAt_phi_one (ihr _ (jL_mem_jH (mem_lset.mpr hu) (mem_lset.mpr hv)) e' he')

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_right_letter

/-- A crossing letter `(0u, 1v)` is a conjugate of the crossing letter by same-side letters. -/
theorem cross_letter_eq {l r : BTree} {u v : List (Fin 2)} (hu : u ∈ l.leaves)
    (hv : v ∈ r.leaves) :
    jL (0 :: u) (1 :: v) = jL (1 :: v) (crossQ r) * (jL (0 :: u) (crossP l) *
      jL (crossP l) (crossQ r) * jL (0 :: u) (crossP l)) * jL (1 :: v) (crossQ r) := by
  have hu' : (0 :: u) ∈ (node l r).leaves := mem_leaves_node.mpr (Or.inl ⟨u, hu, rfl⟩)
  have hv' : (1 :: v) ∈ (node l r).leaves := mem_leaves_node.mpr (Or.inr ⟨v, hv, rfl⟩)
  have hpq1 : ¬ crossP l <+: crossQ r := nprefix_zero_one _ _
  have hpq2 : ¬ crossQ r <+: crossP l := nprefix_one_zero _ _
  have c1 : jL (0 :: u) (crossP l) * jL (crossP l) (crossQ r) * (jL (0 :: u) (crossP l))⁻¹ =
      jL (0 :: u) (crossQ r) :=
    rcl jd2 _ hpq1 hpq2 (mc_jL_right (leaves_eq_or_incomp hu' (crossP_mem l r)))
      (mc_jL_fix (leaves_eq_or_incomp hu' (crossP_mem l r)) (nprefix_zero_one _ _)
        (nprefix_one_zero _ _) hpq1 hpq2)
  have c2 : jL (1 :: v) (crossQ r) * jL (0 :: u) (crossQ r) * (jL (1 :: v) (crossQ r))⁻¹ =
      jL (0 :: u) (1 :: v) :=
    rcl jd2 _ (nprefix_zero_one _ _) (nprefix_one_zero _ _)
      (mc_jL_fix (leaves_eq_or_incomp hv' (crossQ_mem l r)) (nprefix_one_zero _ _)
        (nprefix_zero_one _ _) (nprefix_one_zero _ _) (nprefix_zero_one _ _))
      (mc_jL_right (leaves_eq_or_incomp hv' (crossQ_mem l r)))
  rw [← c2, ← c1, jL_inv, jL_inv]

#audit_axioms GroupApproximation.BooneHigman.Join.cross_letter_eq

/-- The letters of `node l r` have the expansion property at every leaf. -/
theorem felAt_node_letter {l r : BTree}
    (ihl : ∀ σ ∈ jH 2 l.lset, ∀ d ∈ l.leaves, FELAt l σ d)
    (ihr : ∀ σ ∈ jH 2 r.lset, ∀ d ∈ r.leaves, FELAt r σ d) {x y : List (Fin 2)}
    (hx : x ∈ (node l r).leaves) (hy : y ∈ (node l r).leaves) :
    ∀ e ∈ (node l r).leaves, FELAt (node l r) (jL x y) e := by
  have hmul : ∀ a b : higmanVCCommon_Q 2, (∀ e ∈ (node l r).leaves, FELAt (node l r) a e) →
      (∀ e ∈ (node l r).leaves, FELAt (node l r) b e) →
      ∀ e ∈ (node l r).leaves, FELAt (node l r) (a * b) e :=
    fun a b ha hb e he => felAt_mul (hb e he) ha
  have cross : ∀ u ∈ l.leaves, ∀ v ∈ r.leaves, ∀ e ∈ (node l r).leaves,
      FELAt (node l r) (jL (0 :: u) (1 :: v)) e := by
    intro u hu v hv
    rw [cross_letter_eq hu hv]
    have hL := fun e (he : e ∈ (node l r).leaves) =>
      felAt_left_letter (r := r) ihl hu (rightmost_mem l) he
    have hR := fun e (he : e ∈ (node l r).leaves) =>
      felAt_right_letter (l := l) ihr hv (leftmost_mem r) he
    exact hmul _ _ (hmul _ _ hR (hmul _ _ (hmul _ _ hL (fun e he => felAt_cross l r he)) hL)) hR
  rcases mem_leaves_node.mp hx with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩ <;>
    rcases mem_leaves_node.mp hy with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · exact fun e he => felAt_left_letter ihl hu hv he
  · exact cross u hu v hv
  · rw [jL_symm (nprefix_one_zero _ _) (nprefix_zero_one _ _)]
    exact cross v hv u hu
  · exact fun e he => felAt_right_letter ihr hu hv he

#audit_axioms GroupApproximation.BooneHigman.Join.felAt_node_letter

/-- **The fundamental expansion lemma.** -/
theorem fel : ∀ (T : BTree), ∀ σ ∈ jH 2 T.lset, ∀ d ∈ T.leaves, FELAt T σ d
  | .leaf, σ, hσ, d, hd => by
    have h1 : σ = 1 := by
      refine jH_induction (P := fun s => s = 1) rfl ?_ (fun a b ha hb => by rw [ha, hb, one_mul])
        (fun a ha => by rw [ha, inv_one]) hσ
      intro x hx y hy
      simp only [mem_lset, leaves, List.mem_singleton] at hx hy
      rw [hx, hy]
      exact jL_self _
    rw [h1]
    exact felAt_of_mem hd (Subgroup.one_mem _)
  | .node l r, σ, hσ, d, hd => by
    have ihl := fel l
    have ihr := fel r
    refine jH_induction_mon (P := fun s => ∀ e ∈ (node l r).leaves, FELAt (node l r) s e)
      (fun e he => felAt_of_mem he (Subgroup.one_mem _)) ?_
      (fun a b ha hb e he => felAt_mul (hb e he) ha) hσ d hd
    intro x hx y hy
    exact felAt_node_letter ihl ihr (mem_lset.mp hx) (mem_lset.mp hy)

#audit_axioms GroupApproximation.BooneHigman.Join.fel

end GroupApproximation.BooneHigman.Join
