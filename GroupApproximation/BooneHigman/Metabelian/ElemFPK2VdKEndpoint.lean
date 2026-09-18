import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKAssemble
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Van der Kallen's action: the isolated row-extension input

Lane `bh-met-50`.  `ElemFPK2VdKParabolic` and `ElemFPK2VdKAssemble` build van der Kallen's action.
They prove unconditionally the set `Ω`, the action of `St_n(R)`, the column roots, the case split
`vdkT` and compatibility.  They also prove every relator that avoids row roots.  The only input
left is a `VdKRowData`: permutations for the row roots `x_{last,j}` of the free `P̃`-set
`VdKΩ n R X`, satisfying the five relator families with a row root.

* `VdKRowData.eq_one_of_K2Stab`: over any ring, row data on a nonempty `X` makes
  `K₂(n, R) → K₂(n+1, R)` injective.  `vdkAct` is free, so it separates `(0, 1, ξ₀)`.
* `VdKRowExtensionStatement`: for every prime `p` and `k > 0`, some nonempty `X` carries row data
  at rank `k + 4` over `F_p[s_1, …, s_k]`.
* `stabDiagLastRootAction_of_vdkRowExtension`: this implies `StabDiagLastRootActionStatement`.
  `polyK2StabRangeDiag_of_vdkRowExtension` and `polynomialFpK2Vanishing_of_vdkRowExtension`
  chain it into the existing endpoints.

Truth of `VdKRowExtensionStatement`.  By Bass, `sr(F_p[s_1, …, s_k]) ≤ k + 1`.  Van der Kallen's
theorem gives injective stability `K₂(n) → K₂(n+1)` for `n ≥ sr + 2`, so it holds at `n = k + 4`.
Then `P̃ = R^n ⋊ St_n(R)` embeds in `G = St_{n+1}(R)`, so `G` is a free left `P̃`-set.  Take
`X = P̃ \ G` and transport the left action of `G` along `G ≃ P̃ × X`.  Left multiplication by the
row roots then satisfies every field.  The statement therefore implies injective stability on all
of `K₂` at rank `k + 4`.  It is stronger in logical content than the `ker ev₀` gap, and smaller in
proof content: no relator for column roots or `St_n` roots remains.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- Row data on a nonempty `X` gives injectivity of `K₂(n, R) → K₂(n+1, R)`, over any ring. -/
theorem VdKRowData.eq_one_of_K2Stab {R : Type*} [Ring R] {n : ℕ} {X : Type*}
    (D : VdKRowData n R X) (x₀ : X) (u : K2n n R) (hu : K2Stab n R u = 1) : u = 1 :=
  eq_one_of_K2Stab_of_lastRootAction D.toLastRootAction (fun _ => True)
    ((0 : Fin n → R), (1 : St n R), x₀)
    (fun v _ hfix => Subtype.ext (vdkAct_eq_one_of_fix X x₀ (v : St n R) hfix)) u trivial hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.eq_one_of_K2Stab

/-- The isolated stable-range input: row-root permutations of the free `P̃`-set satisfying the
row relators, at rank `k + 4` over `F_p[s_1, …, s_k]`. -/
def VdKRowExtensionStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
    ∃ X : Type, Nonempty X ∧ Nonempty (VdKRowData (k + 4) (MvPolynomial (Fin k) (ZMod p)) X)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowExtensionStatement

/-- The row-extension input yields the last-root action gap of lane `bh-met-35`. -/
theorem stabDiagLastRootAction_of_vdkRowExtension (h : VdKRowExtensionStatement) :
    StabDiagLastRootActionStatement := by
  intro p hp k hk
  obtain ⟨X, ⟨x₀⟩, ⟨D⟩⟩ := h p hp k hk
  refine ⟨VdKΩ (k + 4) (MvPolynomial (Fin k) (ZMod p)) X, D.toLastRootAction,
    ((0 : Fin (k + 4) → MvPolynomial (Fin k) (ZMod p)),
      (1 : St (k + 4) (MvPolynomial (Fin k) (ZMod p))), x₀), ?_⟩
  intro u _ hfix
  exact Subtype.ext
    (vdkAct_eq_one_of_fix X x₀ (u : St (k + 4) (MvPolynomial (Fin k) (ZMod p))) hfix)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stabDiagLastRootAction_of_vdkRowExtension

/-- The row-extension input gives the diagonal stable-range statement. -/
theorem polyK2StabRangeDiag_of_vdkRowExtension (h : VdKRowExtensionStatement) :
    PolyK2StabRangeDiagStatement :=
  polyK2StabRangeDiag_of_lastRootAction (stabDiagLastRootAction_of_vdkRowExtension h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiag_of_vdkRowExtension

/-- The row-extension input, with the nilpotent and field inputs, gives polynomial `K₂`
vanishing over `F_p`. -/
theorem polynomialFpK2Vanishing_of_vdkRowExtension (h : VdKRowExtensionStatement)
    (hnil : PolyK2NilPosStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_lastRootAction (stabDiagLastRootAction_of_vdkRowExtension h) hnil
    hfield

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_vdkRowExtension

end GroupApproximation.BooneHigman.Metabelian.ElemFP
