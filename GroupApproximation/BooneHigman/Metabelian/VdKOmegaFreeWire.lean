import GroupApproximation.BooneHigman.Metabelian.VdKOmegaFreeCoset
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaFreeRow
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaRhoWire
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaWire
import GroupApproximation.BooneHigman.Metabelian.VdKParPresKernel
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# `vdkOmegaFree`, part 4: the residual `vdkOmegaRho_HasFree` is exactly injectivity of `stab`

Lane `bh-met-93j`.

**LOUD: what this file is, and what it is not.**

* **NO-GO for a choice "without vdK".**  For `3 ≤ n`, `vdkOmegaRho_HasFree n R` IMPLIES
  `Injective (stab n R)` (`vdkOmegaFree_stab_injective_of_hasFree`, already a composite of
  existing wires).  So no choice of `(X, X', x₀, θ, σ)` can avoid proving van der Kallen
  injectivity: any such choice would prove it.
* **The converse, formalized here** (it was flagged "not formalized" in `VdKOmegaRhoWire`):
  `Injective (stab n R) → vdkOmegaRho_HasFree n R` for `2 ≤ n`
  (`vdkOmegaFree_hasFree_of_stab_injective`).  The choice is explicit and not circular as a
  construction: `X = Π(P̃) \ St_{n+1}(R)`, `X' = Π⁻(P̃⁻) \ St_{n+1}(R)` (orbit spaces of
  the two parabolic maps `Π`, `Π⁻`, NOT `St_{n+1}` itself as `Ω`), `Ψ = E'⁻¹ ∘ E` with
  `E (p, x) = Π p · out x`, and `θ`, `σ` read off from `Ψ` (`VdKOmegaFreeDecomp`).
  `MixedOne` is then the Steinberg relation `⁅x_{i,last}(1), x_{last,j}(1)⁆ = x_{ij}(1)` in
  `St_{n+1}(R)`, carried through `E` (`vdkOmegaFree_commutator_eq`).  Injectivity of `stab`
  is used, and needed, to make `E` and `E'` bijections.
* Hence **EQUIVALENT, not progress on vdK**: `vdkOmegaFree_hasFree_iff` (`3 ≤ n`) and
  `vdkOmegaFree_statement_iff : vdkOmegaRho_Statement ↔ vdkParPres_NoHiddenRelStatement`.
* **The one TRUE, UNCONDITIONAL special case**: `vdkOmegaFree_zmodStatement`, i.e.
  `vdkOmegaRho_HasFree N (ZMod p)` for `p` prime and `5 ≤ N`.  It is not circular:
  injectivity of `stab` over `𝔽_p` comes from the independent `K₂(𝔽_p)` vanishing
  (`vdkRowExt_K2Stab_injective_zmod`).  It is a special case (hence weaker, and not
  equivalent as far as is known) of `vdkOmegaRho_Statement`, which quantifies over all
  commutative rings of bounded stable rank; it makes no progress on the general case.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colRoot rowRoot)
open scoped commutatorElement

section Wire

variable {n : ℕ} {R : Type} [CommRing R]

/-- **No-go.**  For `3 ≤ n`, the residual forces van der Kallen injectivity. -/
theorem vdkOmegaFree_stab_injective_of_hasFree (hn : 3 ≤ n) (h : vdkOmegaRho_HasFree n R) :
    Function.Injective (stab n R) :=
  vdkOmega_stab_injective_of_hasOmega (vdkOmegaBuild_hasOmega_of_hasOmegaOne hn
    (vdkOmegaSet_hasOmegaOne_of_hasRows (vdkOmegaRho_hasRows_of_hasFree h)))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_stab_injective_of_hasFree

theorem vdkOmegaFree_Pi_injective (hinj : Function.Injective (stab n R)) :
    Function.Injective (vdkParPres_Pi (n := n) (R := R)) :=
  vdkParPres_noHiddenRel_iff_injective_Pi.mp (vdkParPres_noHiddenRel_iff_stab_injective.mpr hinj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Pi_injective

theorem vdkOmegaFree_Pi_inr_eq (g : St n R) :
    vdkParPres_Pi (SemidirectProduct.inr g : vdkParPres_Tilde n R) =
      vdkOmega_PiMinus (SemidirectProduct.inr g : vdkOmega_TildeMinus n R) :=
  (vdkParPres_Pi_inr g).trans (vdkOmega_PiMinus_inr g).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Pi_inr_eq

variable (n R) in
/-- `X = Π(P̃) \ St_{n+1}(R)`. -/
abbrev vdkOmegaFree_X : Type := vdkOmegaFree_Orb (vdkParPres_Pi (n := n) (R := R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_X

variable (n R) in
/-- `X' = Π⁻(P̃⁻) \ St_{n+1}(R)`. -/
abbrev vdkOmegaFree_X' : Type := vdkOmegaFree_Orb (vdkOmega_PiMinus (n := n) (R := R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_X'

/-- `Ψ = E'⁻¹ ∘ E : P̃ × X ≃ P̃⁻ × X'`. -/
noncomputable def vdkOmegaFree_Psi0 (hinj : Function.Injective (stab n R)) :
    vdkParPres_Tilde n R × vdkOmegaFree_X n R ≃ vdkOmega_TildeMinus n R × vdkOmegaFree_X' n R :=
  vdkOmegaFree_Psi vdkParPres_Pi vdkOmega_PiMinus (vdkOmegaFree_Pi_injective hinj)
    (vdkOmegaFree_PiMinus_injective hinj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Psi0

theorem vdkOmegaFree_Psi0_equivariant (hinj : Function.Injective (stab n R)) :
    vdkOmegaFree_Equivariant (vdkOmegaFree_Psi0 hinj) :=
  vdkOmegaFree_Psi_equivariant vdkParPres_Pi vdkOmega_PiMinus (vdkOmegaFree_Pi_injective hinj)
    (vdkOmegaFree_PiMinus_injective hinj) vdkOmegaFree_Pi_inr_eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_Psi0_equivariant

/-- **The chosen `θ`.** -/
noncomputable def vdkOmegaFree_theta0 (hinj : Function.Injective (stab n R)) :
    Multiplicative (Fin n → R) × vdkOmegaFree_X n R ≃
      Multiplicative (Fin n → R) × vdkOmegaFree_X' n R :=
  vdkOmegaFree_theta (vdkOmegaFree_Psi0_equivariant hinj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_theta0

/-- **The chosen `σ`.** -/
noncomputable def vdkOmegaFree_sigma0 (hinj : Function.Injective (stab n R)) :
    Multiplicative (Fin n → R) × vdkOmegaFree_X n R → St n R :=
  vdkOmegaFree_sigma (vdkOmegaFree_Psi0 hinj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_sigma0

theorem vdkOmegaFree_fwd0 (hinj : Function.Injective (stab n R))
    (ω : vdkParPres_Tilde n R × vdkOmegaFree_X n R) :
    vdkOmegaRho_fwd vdkParPres_act vdkOmega_rowAct (vdkOmegaFree_theta0 hinj)
      (vdkOmegaFree_sigma0 hinj) ω = vdkOmegaFree_Psi0 hinj ω :=
  vdkOmegaFree_fwd_eq (vdkOmegaFree_Psi0_equivariant hinj) ω

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_fwd0

theorem vdkOmegaFree_bwd0 (hinj : Function.Injective (stab n R))
    (ω' : vdkOmega_TildeMinus n R × vdkOmegaFree_X' n R) :
    vdkOmegaRho_bwd vdkParPres_act vdkOmega_rowAct (vdkOmegaFree_theta0 hinj)
      (vdkOmegaFree_sigma0 hinj) ω' = (vdkOmegaFree_Psi0 hinj).symm ω' :=
  vdkOmegaFree_bwd_eq (vdkOmegaFree_Psi0_equivariant hinj) ω'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_bwd0

/-- `E` carries `α p` to left multiplication by `Π p`. -/
theorem vdkOmegaFree_inter_alpha (p : vdkParPres_Tilde n R) :
    vdkOmegaFree_Inter (vdkOmegaFree_E (vdkParPres_Pi (n := n) (R := R)))
      (vdkOmegaSet_alpha (vdkOmegaFree_X n R) p) (vdkParPres_Pi p) := by
  intro ω
  exact vdkOmegaFree_E_mul vdkParPres_Pi p ω.1 ω.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_inter_alpha

/-- `E` carries `β q` to left multiplication by `Π⁻ q`: `β` is conjugate, via `Ψ`, to left
multiplication, and `E' ∘ Ψ = E`. -/
theorem vdkOmegaFree_inter_beta (hinj : Function.Injective (stab n R))
    (q : vdkOmega_TildeMinus n R) :
    vdkOmegaFree_Inter (vdkOmegaFree_E (vdkParPres_Pi (n := n) (R := R)))
      (vdkOmegaRho_beta (vdkOmegaFree_X n R) (vdkOmegaFree_X' n R) (vdkOmegaFree_theta0 hinj)
        (vdkOmegaFree_sigma0 hinj) q) (vdkOmega_PiMinus q) := by
  intro ω
  rw [vdkOmegaRho_beta_apply, vdkOmegaFree_fwd0 hinj, vdkOmegaFree_bwd0 hinj]
  exact vdkOmegaFree_E_Psi_symm_mul vdkParPres_Pi vdkOmega_PiMinus
    (vdkOmegaFree_Pi_injective hinj) (vdkOmegaFree_PiMinus_injective hinj) q ω

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_inter_beta

/-- **`MixedOne` for the orbit-space choice**, for every `i₀ ≠ j₀`. -/
theorem vdkOmegaFree_mixedOne (hinj : Function.Injective (stab n R)) (i₀ j₀ : Fin n)
    (h : i₀ ≠ j₀) :
    vdkOmegaSet_MixedOne (vdkOmegaFree_X n R)
      (vdkOmegaRho_rho (vdkOmegaFree_X n R) (vdkOmegaFree_X' n R) (vdkOmegaFree_theta0 hinj)
        (vdkOmegaFree_sigma0 hinj)) i₀ j₀ h := by
  unfold vdkOmegaSet_MixedOne
  have ha := vdkOmegaFree_inter_alpha (n := n) (R := R)
    (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i₀ (1 : R))))
  rw [vdkOmega_Pi_inl_single] at ha
  have hb := vdkOmegaFree_inter_beta hinj
    (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single j₀ (1 : R))))
  rw [vdkOmega_PiMinus_inl_single] at hb
  have hc := vdkOmegaFree_inter_alpha (n := n) (R := R) (vdkParPres_inr (x i₀ j₀ h (1 : R)))
  rw [vdkParPres_Pi_inr] at hc
  exact vdkOmegaFree_commutator_eq (vdkOmegaFree_E_injective _ (vdkOmegaFree_Pi_injective hinj))
    ha hb hc (vdkOmegaFree_mixed_root i₀ j₀ h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_mixedOne

/-- **The converse (EQUIVALENT direction, not progress on vdK).**  Injective `stab` gives the
residual, with the explicit orbit-space choice. -/
theorem vdkOmegaFree_hasFree_of_stab_injective (hn : 2 ≤ n)
    (hinj : Function.Injective (stab n R)) : vdkOmegaRho_HasFree n R := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := Fin.ne_of_val_ne (by simp)
  exact ⟨vdkOmegaFree_X n R, vdkOmegaFree_X' n R, Quotient.mk _ (1 : St (n + 1) R),
    vdkOmegaFree_theta0 hinj, vdkOmegaFree_sigma0 hinj, _, _, h01,
    vdkOmegaFree_mixedOne hinj _ _ h01⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_hasFree_of_stab_injective

/-- **EQUIVALENT.**  For `3 ≤ n` the residual is exactly van der Kallen injectivity. -/
theorem vdkOmegaFree_hasFree_iff (hn : 3 ≤ n) :
    vdkOmegaRho_HasFree n R ↔ Function.Injective (stab n R) :=
  ⟨vdkOmegaFree_stab_injective_of_hasFree hn, vdkOmegaFree_hasFree_of_stab_injective (by omega)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_hasFree_iff

end Wire

/-- **EQUIVALENT.**  `vdkOmegaRho_Statement` is `vdkParPres_NoHiddenRelStatement`. -/
theorem vdkOmegaFree_statement_iff :
    vdkOmegaRho_Statement ↔ vdkParPres_NoHiddenRelStatement := by
  refine ⟨vdkOmegaRho_noHiddenRelStatement_of_statement, fun h ↦ ?_⟩
  intro R _ r hr
  exact vdkOmegaFree_hasFree_of_stab_injective (by omega)
    (vdkParPres_noHiddenRel_iff_stab_injective.mp (h R r hr))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_statement_iff

/-- **TRUE, unconditional, a special case.**  The residual over `𝔽_p`, `5 ≤ N`. -/
theorem vdkOmegaFree_hasFree_zmod {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    vdkOmegaRho_HasFree N (ZMod p) :=
  vdkOmegaFree_hasFree_of_stab_injective (by omega)
    (vdkParPres_noHiddenRel_iff_stab_injective.mp
      (vdkParPres_noHiddenRel_iff_K2Stab_injective.mpr (vdkRowExt_K2Stab_injective_zmod hp hN)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_hasFree_zmod

/-- **The isolated weaker Statement** (a special case of `vdkOmegaRho_Statement`: fields
`𝔽_p` have stable rank `1`, and `5 ≤ N` is within `r + 3`).  **TRUE, proved below.** -/
def vdkOmegaFree_ZModStatement : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (N : ℕ), 5 ≤ N → vdkOmegaRho_HasFree N (ZMod p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_ZModStatement

theorem vdkOmegaFree_zmodStatement : vdkOmegaFree_ZModStatement :=
  fun _ hp _ hN ↦ vdkOmegaFree_hasFree_zmod hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaFree_zmodStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
