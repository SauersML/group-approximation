import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllPath
import GroupApproximation.Meta.AxiomGuard

/-!
# Peeling a path off the pivot (lane bh-met-91x)

Notation as in `EnvelopeHigmanVCOrbitAllComm`.  For incomparable `a, b` and a word `p`,
`higmanVCOrbitAll_path_mem` shows `m(a p, b p)⁻¹ · m(a, b) ∈ K` for every subgroup `K` that
contains the sibling letters `m(a q j, b q j)`, where `q y <+: p` and `j ≠ y`.  The proof
is by induction on `p = y :: p'`.  Split `m(a, b) = A₀ · m(a y, b y) · B₀` over
`List.finRange d = l₁ ++ y :: l₂`.  The letters of `A₀` commute with `m(a y p', b y p')`
(`higmanVCOrbitAll_centP`), so `higmanVCOrbitAll_elim2` moves the inverse pivot past `A₀`.
The induction hypothesis then applies to `(a y, b y, p')`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- For `j ≠ y`, `m(a j, b j)` commutes with `m(a y p, b y p)`. -/
theorem higmanVCOrbitAll_centP {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {y j : Fin d} (hj : j ≠ y) (p : List (Fin d)) :
    higmanVCCommon_mk d (FreeGroup.of (a ++ [j], b ++ [j])) ∈ Subgroup.centralizer
      {higmanVCCommon_mk d (FreeGroup.of (a ++ [y] ++ p, b ++ [y] ++ p))} := by
  have qa : a <+: a ++ [j] := List.prefix_append a [j]
  have qb : b <+: b ++ [j] := List.prefix_append b [j]
  have pa : a <+: a ++ [y] ++ p := (List.prefix_append a [y]).trans (List.prefix_append _ p)
  have pb : b <+: b ++ [y] ++ p := (List.prefix_append b [y]).trans (List.prefix_append _ p)
  have ra : a ++ [y] <+: a ++ [y] ++ p := List.prefix_append _ p
  have rb : b ++ [y] <+: b ++ [y] ++ p := List.prefix_append _ p
  have h1 : ¬ a ++ [j] <+: a ++ [y] ++ p := higmanVCOrbitAll_branch hj (List.prefix_refl _) ra
  have h2 : ¬ a ++ [y] ++ p <+: a ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) ra (List.prefix_refl _)
  have h7 : ¬ b ++ [j] <+: b ++ [y] ++ p := higmanVCOrbitAll_branch hj (List.prefix_refl _) rb
  have h8 : ¬ b ++ [y] ++ p <+: b ++ [j] :=
    higmanVCOrbitAll_branch (Ne.symm hj) rb (List.prefix_refl _)
  exact higmanVCOrbitAll_comm (higmanVCOrbitGen_incomp hab hba pa pb)
    (higmanVCOrbitGen_incomp hba hab pb pa) (higmanVCOrbitGen_incomp hab hba qa qb)
    (higmanVCOrbitGen_incomp hba hab qb qa) h1 h2 (higmanVCOrbitGen_incomp hab hba qa pb)
    (higmanVCOrbitGen_incomp hba hab pb qa) (higmanVCOrbitGen_incomp hba hab qb pa)
    (higmanVCOrbitGen_incomp hab hba pa qb) h7 h8

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_centP

/-- Moving an inverse pivot `P⁻¹` past a factor `A` that commutes with `P`. -/
theorem higmanVCOrbitAll_elim2 {G : Type*} [Group G] {P A M B : G} (hc : A * P = P * A) :
    P⁻¹ * (A * (M * B)) = A * (P⁻¹ * M) * B :=
  calc P⁻¹ * (A * (M * B)) = P⁻¹ * (A * P) * (P⁻¹ * M) * B := by group
    _ = A * (P⁻¹ * M) * B := by rw [hc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_elim2

/-- A prefix `q y` of `p z` is a prefix of `p`, or else `q = p` and `y = z`. -/
theorem higmanVCOrbitAll_prefix_snoc {d : ℕ} {q p : List (Fin d)} {y z : Fin d}
    (h : q ++ [y] <+: p ++ [z]) : q ++ [y] <+: p ∨ (q = p ∧ y = z) := by
  rcases List.prefix_concat_iff.mp h with h | h
  · obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    exact Or.inr ⟨h1, List.singleton_inj.mp h2⟩
  · exact Or.inl h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_prefix_snoc

/-- **Peeling a path.**  If `K` contains every sibling letter `m(a q j, b q j)` (with
`q y <+: p`, `j ≠ y`), then `m(a p, b p)⁻¹ · m(a, b) ∈ K`. -/
theorem higmanVCOrbitAll_path_mem {d : ℕ} {K : Subgroup (higmanVCCommon_Q d)} :
    ∀ (p a b : List (Fin d)), ¬ a <+: b → ¬ b <+: a →
      (∀ (q : List (Fin d)) (y j : Fin d), q ++ [y] <+: p → j ≠ y →
        higmanVCCommon_mk d (FreeGroup.of (a ++ q ++ [j], b ++ q ++ [j])) ∈ K) →
      (higmanVCCommon_mk d (FreeGroup.of (a ++ p, b ++ p)))⁻¹ *
        higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ K
  | [], a, b, _, _, _ => by
    simp only [List.append_nil, inv_mul_cancel]
    exact K.one_mem
  | y :: p, a, b, hab, hba, hK => by
    obtain ⟨l₁, l₂, hfr⟩ := List.append_of_mem (List.mem_finRange y)
    have hx : y ∉ l₁ ++ l₂ := by
      have hnd := List.nodup_finRange d
      rw [hfr] at hnd
      exact (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1
    have hne1 : ∀ j ∈ l₁, j ≠ y := fun j hj h => hx (List.mem_append_left l₂ (h ▸ hj))
    have hne2 : ∀ j ∈ l₂, j ≠ y := fun j hj h => hx (List.mem_append_right l₁ (h ▸ hj))
    have i1 : ¬ a ++ [y] <+: b ++ [y] :=
      higmanVCOrbitGen_incomp hab hba (List.prefix_append a [y]) (List.prefix_append b [y])
    have i1' : ¬ b ++ [y] <+: a ++ [y] :=
      higmanVCOrbitGen_incomp hba hab (List.prefix_append b [y]) (List.prefix_append a [y])
    have hK0 : ∀ j : Fin d, j ≠ y →
        higmanVCCommon_mk d (FreeGroup.of (a ++ [j], b ++ [j])) ∈ K := by
      intro j hj
      have := hK [] y j ⟨p, rfl⟩ hj
      simp only [List.append_nil] at this
      exact this
    have ih := higmanVCOrbitAll_path_mem p (a ++ [y]) (b ++ [y]) i1 i1' (by
      intro q y' j hq hj
      have e1 : a ++ [y] ++ q ++ [j] = a ++ (y :: q) ++ [j] := by simp
      have e2 : b ++ [y] ++ q ++ [j] = b ++ (y :: q) ++ [j] := by simp
      rw [e1, e2]
      refine hK (y :: q) y' j ?_ hj
      rw [List.cons_append]
      exact List.cons_prefix_cons.mpr ⟨rfl, hq⟩)
    have ea : a ++ y :: p = a ++ [y] ++ p := by simp
    have eb : b ++ y :: p = b ++ [y] ++ p := by simp
    have cA := higmanVCOrbitGen_split_mem a b l₁ fun j hj =>
      higmanVCOrbitAll_centP hab hba (hne1 j hj) p
    have hc := (Subgroup.mem_centralizer_iff.mp cA _ (Set.mem_singleton _)).symm
    rw [ea, eb, higmanVCOrbitAll_split_mid hfr hab hba, higmanVCOrbitAll_elim2 hc]
    exact K.mul_mem (K.mul_mem (higmanVCOrbitGen_split_mem a b l₁ fun j hj => hK0 j (hne1 j hj))
      ih) (higmanVCOrbitGen_split_mem a b l₂ fun j hj => hK0 j (hne2 j hj))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_path_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
