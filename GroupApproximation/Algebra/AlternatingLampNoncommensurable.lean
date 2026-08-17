import GroupApproximation.Algebra.PermutationalWreathSimple
import GroupApproximation.Algebra.FiniteResidualCommensurability

/-!
# The alternating-lamp family is pairwise noncommensurable

**Section 52.3** of the dossier, the separation half.  Two ingredients are
already in place: the finite residual is an isomorphism invariant unchanged by
passage to finite index (`Algebra/FiniteResidualCommensurability`), and the
alternating lamp groups are pairwise non-isomorphic
(`Algebra/PermutationalWreathSimple.alternating_lamp_not_mulEquiv`).  Putting
them together separates the family up to *commensurability*, which is much
stronger than up to isomorphism: no finite-index subgroup of one member is
isomorphic to a finite-index subgroup of another.

The hypothesis is that the residual of each member has already been identified
with its lamp base.  For the compression wreath products that identification is
the exact-radical computation; here it is taken as input, so the separation
mechanism is recorded independently of it.
-/

namespace GroupApproximation

universe v w

/-- **Section 52.3.**  Members of the family whose finite residuals are
alternating lamps of different degree have no isomorphic finite-index
subgroups. -/
theorem not_mulEquiv_finiteIndex_of_alternating_residual
    {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) (hmn : m ≠ n)
    {X : Type v} [DecidableEq X] (hX : Nonempty X)
    {W₁ : Type w} [Group W₁] {W₂ : Type w} [Group W₂]
    {K₁ : Subgroup W₁} [K₁.FiniteIndex] {K₂ : Subgroup W₂} [K₂.FiniteIndex]
    (h₁ : Nonempty (↥((finiteResidual W₁).subgroupOf K₁)
      ≃* Lamp (alternatingGroup (Fin m)) X))
    (h₂ : Nonempty (↥((finiteResidual W₂).subgroupOf K₂)
      ≃* Lamp (alternatingGroup (Fin n)) X)) :
    IsEmpty (K₁ ≃* K₂) := by
  refine not_commensurable_of_finiteResidual_not_mulEquiv ⟨fun e => ?_⟩
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact (alternating_lamp_not_mulEquiv (X := X) hm hn hmn hX).elim
    ((e₁.symm.trans e).trans e₂)

/-- The same statement for the groups themselves: different degrees give
non-isomorphic members. -/
theorem not_mulEquiv_of_alternating_residual
    {m n : ℕ} (hm : 5 ≤ m) (hn : 5 ≤ n) (hmn : m ≠ n)
    {X : Type v} [DecidableEq X] (hX : Nonempty X)
    {W₁ : Type w} [Group W₁] {W₂ : Type w} [Group W₂]
    (h₁ : Nonempty (↥(finiteResidual W₁) ≃* Lamp (alternatingGroup (Fin m)) X))
    (h₂ : Nonempty (↥(finiteResidual W₂) ≃* Lamp (alternatingGroup (Fin n)) X)) :
    IsEmpty (W₁ ≃* W₂) := by
  refine not_mulEquiv_of_finiteResidual_not_mulEquiv ⟨fun e => ?_⟩
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  exact (alternating_lamp_not_mulEquiv (X := X) hm hn hmn hX).elim
    ((e₁.symm.trans e).trans e₂)

end GroupApproximation
