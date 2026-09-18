import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCLeafExpTree
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The symmetric pivots are discharged: residual `W` (lane bh-met-77w)

Notation as in `EnvelopeHigmanVCPivotYReduce`, with pivot `t = (a, b)`, `|a| = n`,
`|b| = n + 1`.

**Symmetric case (proved).**  Call `σ ∈ Q` *symmetric* for `(a, b)`
(`higmanVCLeafExp_Sym`) if `σ ∈ H_D` for some antichain `D` containing both `a ⋆ T` and
`b ⋆ T`, for a tree `T`.  Pattern split (`higmanVCLeafExp_tree_mem`) then gives `t ∈ H_D`,
so `σ t ∈ H_D ⊆ S` (`higmanVCLeafExp_sym_mem_S`).  By pattern refinement
(`higmanVCLeafExp_H_le_star`), it is enough that `σ ∈ H_C` and that `C ⋆ T'` contains
`a ⋆ T` and `b ⋆ T` for some trees `T, T'` (`higmanVCLeafExp_sym_of_star`).

**Residual `W` = `HigmanVCLeafExpStatement`.**  This is Z (`HigmanVCPivotYStatement`) with
the pivot closure required only for NON-symmetric `h ∈ H_C`.  `higmanVCLeafExp_Z_of_W`
proves `W → Z`, and `higmanVCLeafExp_swapSection_of_W_of_tau` wires it into the swap
section via `higmanVCPivotY_swapSection_of_Z_of_tau`.

LOUD, on strength: `Z → W` is immediate, so as Props `W ⇔ Z`, and Z is Higman-strength
(it implies relation completeness).  W is strictly smaller only in PROOF CONTENT: every
symmetric `h` is discharged here without Higman's theorem.  That includes all of `H_C`
whenever `C` (or a pattern refinement of `C`) contains `a ⋆ T ∪ b ⋆ T`.  The remaining
case is where `h`'s leaf structure under `a` and under `b` cannot be matched by one
pattern.  That case needs the conjugation relations genuinely, not just splitting.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `σ` is symmetric for the pivot `(a, b)`: `σ ∈ H_D` for an antichain `D ⊇ a ⋆ T ∪ b ⋆ T`,
with `T` a tree. -/
def higmanVCLeafExp_Sym (d : ℕ) (a b : List (Fin d)) (σ : higmanVCCommon_Q d) : Prop :=
  ∃ D T : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC D ∧ higmanVCLeafExp_IsTree T ∧
    σ ∈ higmanVCTreeNFWitPivot_H d D ∧ ∀ e ∈ T, a ++ e ∈ D ∧ b ++ e ∈ D

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_Sym

/-- **Symmetric discharge.**  A symmetric `σ` satisfies `σ t ∈ S`. -/
theorem higmanVCLeafExp_sym_mem_S {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) {σ : higmanVCCommon_Q d} (hσ : higmanVCLeafExp_Sym d a b σ) :
    σ * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d := by
  obtain ⟨D, T, hD, hT, hσD, hsub⟩ := hσ
  have ht : higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_H d D :=
    higmanVCLeafExp_tree_mem hT a b hab hba fun e he =>
      higmanVCLeafExp_letter_mem_H (hsub e he).1 (hsub e he).2
  exact higmanVCTreeNFWitPivot_mem_S.mpr ⟨1, Subgroup.one_mem _, D, hD,
    σ * higmanVCCommon_mk d (FreeGroup.of (a, b)), Subgroup.mul_mem _ hσD ht, 1,
    Subgroup.one_mem _, by rw [one_mul, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_sym_mem_S

/-- A sufficient criterion for symmetry through pattern refinement of `C`. -/
theorem higmanVCLeafExp_sym_of_star {d : ℕ} {a b : List (Fin d)} {C T' T : Finset (List (Fin d))}
    (hC : higmanVCTreeNFWitPivot_IsAC C) (hT' : higmanVCLeafExp_IsTree T')
    (hT : higmanVCLeafExp_IsTree T)
    (hsub : ∀ e ∈ T, a ++ e ∈ higmanVCLeafExp_star C T' ∧ b ++ e ∈ higmanVCLeafExp_star C T')
    {σ : higmanVCCommon_Q d} (hσ : σ ∈ higmanVCTreeNFWitPivot_H d C) :
    higmanVCLeafExp_Sym d a b σ :=
  ⟨higmanVCLeafExp_star C T', T, higmanVCLeafExp_star_isAC hC (higmanVCLeafExp_tree_isAC hT'),
    hT, higmanVCLeafExp_H_le_star hC hT' hσ, hsub⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_sym_of_star

/-- The pivot closure of `higmanVCPivotY_Closed`, required only for non-symmetric `h`. -/
def higmanVCLeafExp_Closed (d L : ℕ) (a b : List (Fin d)) : Prop :=
  ∀ C : Finset (List (Fin d)), higmanVCTreeNFWitPivot_IsAC C → (∀ c ∈ C, L ≤ c.length) →
    (∃ M : ℕ, ∀ w : List (Fin d), w.length = M → ∃ c ∈ C, c <+: w) →
      ∀ h ∈ higmanVCTreeNFWitPivot_H d C, ¬ higmanVCLeafExp_Sym d a b h →
        h * higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈ higmanVCTreeNFWitPivot_S d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_Closed

/-- **Residual W**: Z restricted to non-symmetric `h`.  LOUD: `W ⇔ Z` as Props (Z implies W
at once); W is strictly smaller in proof content only (the symmetric case is proved). -/
def HigmanVCLeafExpStatement : Prop :=
  ∀ d : ℕ, 1 < d → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ a b : List (Fin d), a.length = n ∧
    b.length = n + 1 ∧ ¬ a <+: b ∧ ¬ b <+: a ∧ higmanVCLeafExp_Closed d (n + 1) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.HigmanVCLeafExpStatement

/-- **`W → Z`.** -/
theorem higmanVCLeafExp_Z_of_W (hW : HigmanVCLeafExpStatement) : HigmanVCPivotYStatement := by
  intro d hd N
  obtain ⟨n, hn, a, b, ha, hb, hab, hba, hcl⟩ := hW d hd N
  refine ⟨n, hn, a, b, ha, hb, hab, hba, ?_⟩
  intro C hC hL hM h hh
  by_cases hs : higmanVCLeafExp_Sym d a b h
  · exact higmanVCLeafExp_sym_mem_S hab hba hs
  · exact hcl C hC hL hM h hh hs

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_Z_of_W

/-- **Wiring.**  `W` and the short-relation section `τ` give the swap section. -/
theorem higmanVCLeafExp_swapSection_of_W_of_tau (hW : HigmanVCLeafExpStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCPivotY_swapSection_of_Z_of_tau (higmanVCLeafExp_Z_of_W hW) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCLeafExp_swapSection_of_W_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
