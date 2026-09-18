import GroupApproximation.BooneHigman.Metabelian.VdKOmegaSetWire
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaRhoCoord
import GroupApproximation.Meta.AxiomGuard

/-!
# Row actions from equivariant bijections, part 2: `RowRel` for free, and the residual

Lane `bh-met-93g`.

**`ρ` IS NOT FULLY CONSTRUCTED HERE.**  What is constructed, unconditionally and explicitly:
from sets `X`, `X'`, a bijection `θ : R^n × X ≃ R^n × X'` and a map
`σ : R^n × X → St_n(R)` we build

* the bijection `Φ = vdkOmegaRho_Phi X X' θ σ : P̃ × X ≃ P̃⁻ × X'`
  (`vdkOmegaRho_equiv`, part 1).  It is `St_n(R)`-equivariant for left multiplication on both
  sides (`vdkOmegaRho_fwd_inr_mul`);
* `β = Φ⁻¹ ∘ (left multiplication of P̃⁻ on P̃⁻ × X') ∘ Φ`, an action of `P̃⁻` on `P̃ × X`
  (`vdkOmegaRho_beta`), and `ρ = β ∘ inl` (`vdkOmegaRho_rho`).

Then, for **every** choice of `(X, X', θ, σ)`:

* `vdkOmega_Agree α β` holds (`vdkOmegaRho_agree`), by equivariance of `Φ`;
* the generator relations `vdkOmegaSet_RowRel X ρ` hold (`vdkOmegaRho_rowRel`).  They are a
  formal consequence of `Agree` and `SemidirectProduct.inl_aut` (`vdkOmegaRho_rowRel_of_agree`).

**The residual** `vdkOmegaRho_HasFree n R`: data `(X, X', x₀, θ, σ)` for which the ONE mixed
identity `vdkOmegaSet_MixedOne X ρ i₀ j₀ h` holds.  `RowRel` no longer needs proof.
`vdkOmegaRho_hasRows_of_hasFree` reduces `vdkOmegaSet_HasRows` to it.

**LOUD: truth, and strength.**  The residual is true exactly when van der Kallen's theorem is.
Take `Ω = St_{n+1}(R)`.  Once `stab` is injective, both `P̃` and `P̃⁻` act freely on `Ω` (look
at the last column, resp. the last row).  Choose transversals: `Ω ≅ P̃ × X` and
`Ω ≅ P̃⁻ × X'`, with `X = P̃\Ω` and `X' = P̃⁻\Ω`.  The composite `P̃ × X ≃ P̃⁻ × X'` is
`St_n(R)`-equivariant, hence of the form `vdkOmegaRho_equiv θ σ` for the `θ`, `σ` read off from
it.  Then `ρ` is the row action of `Ω`, and `MixedOne` is the Steinberg relation
`⁅x_{i,n+1}(1), x_{n+1,j}(1)⁆ = x_{ij}(1)` in `St_{n+1}(R)`.  Conversely
`vdkOmegaRho_Statement → vdkOmega_Statement` is proved below.  So, as a `Prop`, the residual is
**EQUIVALENT** to `vdkOmega_Statement` (and to `vdkOmegaSet_Statement`), **not** strictly
weaker.  The converse transport is **not formalized**.  It is strictly smaller in *proof
content* than `vdkOmegaSet_Statement`: `ρ` is no longer an arbitrary homomorphism, and
`RowRel` is discharged.  What remains is to find `(X, X', θ, σ)`, i.e. the orbit-space gluing of
`Ω`, making one identity hold.  It is **not** the naive model: `X = X'`, `θ = id`, `σ = 1`
(and random `θ`, `σ`) fail `MixedOne` (checked numerically, `$SP/bh-met-93g/check.py`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section RowRel

variable {n : ℕ} {R : Type*} [CommRing R] (X : Type*)

/-- **`RowRel` from `Agree`.**  If an action `β` of `P̃⁻` on `P̃ × X` agrees with the explicit `α`
on `St_n(R)`, then `ρ = β ∘ inl` satisfies the generator relations. -/
theorem vdkOmegaRho_rowRel_of_agree
    (β : vdkOmega_TildeMinus n R →* Equiv.Perm (vdkParPres_Tilde n R × X))
    (hagree : vdkOmega_Agree (vdkOmegaSet_alpha X) β) :
    vdkOmegaSet_RowRel X (β.comp SemidirectProduct.inl) := by
  intro i j hij c k b
  have e := SemidirectProduct.inl_aut (φ := vdkOmega_rowAct) (x i j hij c)
    (Multiplicative.ofAdd (Pi.single k b))
  have e' : β (SemidirectProduct.inr (x i j hij c)) =
      vdkOmegaSet_alpha X (vdkParPres_inr (x i j hij c)) :=
    (hagree (x i j hij c)).symm
  simp only [MonoidHom.comp_apply]
  rw [e]
  simp only [map_mul, map_inv]
  rw [e']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_rowRel_of_agree

end RowRel

section Rho

variable {n : ℕ} {R : Type*} [CommRing R] (X X' : Type*)
  (θ : Multiplicative (Fin n → R) × X ≃ Multiplicative (Fin n → R) × X')
  (σ : Multiplicative (Fin n → R) × X → St n R)

/-- **The explicit `St_n(R)`-equivariant bijection** `Φ : P̃ × X ≃ P̃⁻ × X'`. -/
def vdkOmegaRho_Phi : vdkParPres_Tilde n R × X ≃ vdkOmega_TildeMinus n R × X' :=
  vdkOmegaRho_equiv vdkParPres_act vdkOmega_rowAct θ σ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_Phi

/-- **The `β`.**  Left multiplication of `P̃⁻` on `P̃⁻ × X'`, transported along `Φ`. -/
def vdkOmegaRho_beta : vdkOmega_TildeMinus n R →* Equiv.Perm (vdkParPres_Tilde n R × X) :=
  (vdkOmegaRho_Phi X X' θ σ).symm.permCongrHom.toMonoidHom.comp
    (vdkOmegaRho_left (vdkOmega_TildeMinus n R) X')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_beta

theorem vdkOmegaRho_beta_apply (q : vdkOmega_TildeMinus n R) (ω : vdkParPres_Tilde n R × X) :
    vdkOmegaRho_beta X X' θ σ q ω =
      vdkOmegaRho_bwd vdkParPres_act vdkOmega_rowAct θ σ
        (q * (vdkOmegaRho_fwd vdkParPres_act vdkOmega_rowAct θ σ ω).1,
          (vdkOmegaRho_fwd vdkParPres_act vdkOmega_rowAct θ σ ω).2) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_beta_apply

/-- **The row action** `ρ = β ∘ inl`. -/
def vdkOmegaRho_rho :
    Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X) :=
  (vdkOmegaRho_beta X X' θ σ).comp
    (SemidirectProduct.inl : Multiplicative (Fin n → R) →* vdkOmega_TildeMinus n R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_rho

/-- **`Agree`, for free.**  `β` agrees with the explicit `α` on `St_n(R)`. -/
theorem vdkOmegaRho_agree :
    vdkOmega_Agree (vdkOmegaSet_alpha X) (vdkOmegaRho_beta X X' θ σ) := by
  intro g
  refine Equiv.ext fun ω ↦ ?_
  obtain ⟨p, y⟩ := ω
  exact (vdkOmegaRho_bwd_inr_mul_fwd (φ := vdkParPres_act) (φ' := vdkOmega_rowAct)
    θ σ g p y).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_agree

/-- **`RowRel`, for free.**  `ρ` satisfies the generator relations for every `(X, X', θ, σ)`. -/
theorem vdkOmegaRho_rowRel : vdkOmegaSet_RowRel X (vdkOmegaRho_rho X X' θ σ) :=
  vdkOmegaRho_rowRel_of_agree X (vdkOmegaRho_beta X X' θ σ) (vdkOmegaRho_agree X X' θ σ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_rowRel

end Rho

/-- **The residual data.**  Sets `X`, `X'` (with a point of `X`), a bijection
`θ : R^n × X ≃ R^n × X'` and a map `σ : R^n × X → St_n(R)`, such that the row action
`vdkOmegaRho_rho X X' θ σ` satisfies ONE mixed identity.  (`RowRel` holds automatically.) -/
def vdkOmegaRho_HasFree (n : ℕ) (R : Type) [CommRing R] : Prop :=
  ∃ (X X' : Type) (_ : X)
    (θ : Multiplicative (Fin n → R) × X ≃ Multiplicative (Fin n → R) × X')
    (σ : Multiplicative (Fin n → R) × X → St n R) (i₀ j₀ : Fin n) (hij : i₀ ≠ j₀),
    vdkOmegaSet_MixedOne X (vdkOmegaRho_rho X X' θ σ) i₀ j₀ hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_HasFree

/-- **The reduction.**  Residual data give row data (`RowRel` is `vdkOmegaRho_rowRel`). -/
theorem vdkOmegaRho_hasRows_of_hasFree {n : ℕ} {R : Type} [CommRing R]
    (h : vdkOmegaRho_HasFree n R) : vdkOmegaSet_HasRows n R := by
  obtain ⟨X, X', x₀, θ, σ, i₀, j₀, hij, hone⟩ := h
  exact ⟨X, x₀, vdkOmegaRho_rho X X' θ σ, vdkOmegaRho_rowRel X X' θ σ, i₀, j₀, hij, hone⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_hasRows_of_hasFree

/-- **The residual.**  For every commutative ring `R` of stable rank `≤ r` there are residual
data for `n = r + 3`.  LOUD: **equivalent** to `vdkOmega_Statement` as a `Prop` (see the module
docstring; only the reduction direction is formalized), smaller in proof content than
`vdkOmegaSet_Statement`. -/
def vdkOmegaRho_Statement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkOmegaRho_HasFree (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_Statement

/-- **Endpoint.**  The residual gives `vdkOmegaSet_Statement`. -/
theorem vdkOmegaRho_omegaSetStatement_of_statement (h : vdkOmegaRho_Statement) :
    vdkOmegaSet_Statement := by
  intro R _ r hr
  exact vdkOmegaRho_hasRows_of_hasFree (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_omegaSetStatement_of_statement

/-- **Endpoint.**  The residual gives `vdkOmega_Statement`. -/
theorem vdkOmegaRho_omegaStatement_of_statement (h : vdkOmegaRho_Statement) :
    vdkOmega_Statement :=
  vdkOmegaSet_omegaStatement_of_statement (vdkOmegaRho_omegaSetStatement_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_omegaStatement_of_statement

/-- **Endpoint.**  The residual gives `vdkParPres_NoHiddenRelStatement`. -/
theorem vdkOmegaRho_noHiddenRelStatement_of_statement (h : vdkOmegaRho_Statement) :
    vdkParPres_NoHiddenRelStatement :=
  vdkOmegaSet_noHiddenRelStatement_of_statement (vdkOmegaRho_omegaSetStatement_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaRho_noHiddenRelStatement_of_statement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
