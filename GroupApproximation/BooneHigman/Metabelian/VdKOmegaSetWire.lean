import GroupApproximation.BooneHigman.Metabelian.VdKOmegaSetAlpha
import GroupApproximation.BooneHigman.Metabelian.VdKOmegaBuildWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Building `Ω` on `P̃ × X`, part 3: the residual `vdkOmegaSet_Statement` and its wiring

Lane `bh-met-93a`.

**`Ω` IS ONLY PARTLY CONSTRUCTED HERE.**  The carrier is explicit, `Ω = P̃ × X` with `X` any set.
Its `α` is explicit (left multiplication on `P̃`, `vdkOmegaSet_alpha`) and does not use `stab`
or `St_{n+1}(R)`.  What is left open is the row action `ρ : R^n →* Perm Ω` (together with `X`).

**What is discharged, unconditionally**, compared with `vdkOmegaBuild_HasOmegaOne`:

* the choice of `α` (explicit);
* the choice of `ω₀`, and freeness of `St_n(R)` at `ω₀` (`vdkOmegaSet_alpha_free`, any
  `(1, x₀)`);
* the construction of `β` and the clause `vdkOmega_Agree` (`vdkOmegaSet_beta`,
  `vdkOmegaSet_agree`);
* the homomorphism condition of `β` for *all* `g : St_n(R)` and *all* row vectors `w`.  It is
  reduced to Steinberg generators `x_{ij}(c)` and unit vectors `b e_k` (`vdkOmegaSet_RowRel`),
  via a subgroup argument and `Pi.single_induction`.

**The residual** `vdkOmegaSet_HasRows n R`: a set `X` with a point, a row action `ρ` satisfying
the generator relations `vdkOmegaSet_RowRel`, and ONE mixed identity
`⁅x_{i₀,last}(1), ρ(e_{j₀})⁆ = x_{i₀ j₀}(1)` (`vdkOmegaSet_MixedOne`).

**LOUD: truth, and strength.**  The residual is true exactly when van der Kallen's theorem is.
Take `Ω = St_{n+1}(R)` with left multiplication.  Once `stab` is injective, `Π : P̃ → St_{n+1}`
is injective (look at the last column).  So `P̃` acts freely, and `Ω ≅ P̃ × X` as `P̃`-sets,
with `X = Π(P̃)\St_{n+1}(R)`.  Transport the rows `rowVec w` along this bijection to get `ρ`.
`RowRel` is `stab_conj_rowVec`, and `MixedOne` is the Steinberg relation in `St_{n+1}(R)`.
Conversely `vdkOmegaSet_Statement → vdkOmega_Statement` is proved below.  So, as a `Prop`, the
residual is **EQUIVALENT** to `vdkOmega_Statement`, **not** strictly weaker.  (Both are true,
so no true statement is strictly weaker.)  That converse transport is **not formalized**.  The
residual is strictly smaller in *proof content*: the four items above no longer need proof.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] (X : Type*)

/-- The one mixed identity for a row action `ρ` on `P̃ × X`:
`⁅x_{i₀,last}(1), ρ(e_{j₀})⁆ = x_{i₀ j₀}(1)`.  Here `x_{i₀,last}(1)` acts through the explicit
`α`, i.e. by left multiplication by `inl e_{i₀}`. -/
def vdkOmegaSet_MixedOne
    (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X))
    (i₀ j₀ : Fin n) (h : i₀ ≠ j₀) : Prop :=
  ⁅vdkOmega_cv (vdkOmegaSet_alpha X) (Pi.single i₀ 1),
      ρ (Multiplicative.ofAdd (Pi.single j₀ 1))⁆ =
    vdkOmegaSet_alpha X (vdkParPres_inr (x i₀ j₀ h 1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_MixedOne

/-- **The residual data.**  A pointed set `X` and a row action `ρ` on `P̃ × X` satisfying the
generator relations and one mixed identity. -/
def vdkOmegaSet_HasRows (n : ℕ) (R : Type) [CommRing R] : Prop :=
  ∃ (X : Type) (_ : X)
    (ρ : Multiplicative (Fin n → R) →* Equiv.Perm (vdkParPres_Tilde n R × X)),
    vdkOmegaSet_RowRel X ρ ∧
      ∃ (i₀ j₀ : Fin n) (h : i₀ ≠ j₀), vdkOmegaSet_MixedOne X ρ i₀ j₀ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_HasRows

/-- **The construction.**  Row data give `Ω = P̃ × X`, the explicit `α`, the glued `β` and
`ω₀ = (1, x₀)`, with all three clauses of `vdkOmegaBuild_HasOmegaOne`. -/
theorem vdkOmegaSet_hasOmegaOne_of_hasRows {n : ℕ} {R : Type} [CommRing R]
    (h : vdkOmegaSet_HasRows n R) : vdkOmegaBuild_HasOmegaOne n R := by
  obtain ⟨X, x₀, ρ, hrel, i₀, j₀, h0, hone⟩ := h
  have hall := vdkOmegaSet_compatAt_all X ρ hrel
  refine ⟨vdkParPres_Tilde n R × X, vdkOmegaSet_alpha X, vdkOmegaSet_beta X ρ hall, (1, x₀),
    vdkOmegaSet_agree X ρ hall, ⟨i₀, j₀, h0, ?_⟩, vdkOmegaSet_alpha_free X x₀⟩
  change ⁅vdkOmega_cv (vdkOmegaSet_alpha X) (Pi.single i₀ 1),
      vdkOmega_rv (vdkOmegaSet_beta X ρ hall) (Pi.single j₀ 1)⁆ =
    vdkOmegaSet_alpha X (vdkParPres_inr (x i₀ j₀ h0 1))
  rw [vdkOmegaSet_rv_beta]
  exact hone

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_hasOmegaOne_of_hasRows

/-- **The residual.**  For every commutative ring `R` of stable rank `≤ r` there are a pointed
set `X` and a row action `ρ` on `P̃ × X` (`P̃ = R^{r+3} ⋊ St_{r+3}(R)`) satisfying the
generator relations and one mixed identity.  LOUD: **equivalent** to `vdkOmega_Statement` (see
the module docstring; only the reduction direction is formalized), smaller in proof content. -/
def vdkOmegaSet_Statement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkOmegaSet_HasRows (r + 3) R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_Statement

/-- **Endpoint.**  The residual gives `vdkOmegaBuild_Statement`. -/
theorem vdkOmegaSet_buildStatement_of_statement (h : vdkOmegaSet_Statement) :
    vdkOmegaBuild_Statement := by
  intro R _ r hr
  exact vdkOmegaSet_hasOmegaOne_of_hasRows (h R r hr)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_buildStatement_of_statement

/-- **Endpoint.**  The residual gives `vdkOmega_Statement`. -/
theorem vdkOmegaSet_omegaStatement_of_statement (h : vdkOmegaSet_Statement) :
    vdkOmega_Statement :=
  vdkOmegaBuild_omegaStatement_of_statement (vdkOmegaSet_buildStatement_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_omegaStatement_of_statement

/-- **Endpoint.**  The residual gives `vdkParPres_NoHiddenRelStatement`. -/
theorem vdkOmegaSet_noHiddenRelStatement_of_statement (h : vdkOmegaSet_Statement) :
    vdkParPres_NoHiddenRelStatement :=
  vdkOmegaBuild_noHiddenRelStatement_of_statement (vdkOmegaSet_buildStatement_of_statement h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmegaSet_noHiddenRelStatement_of_statement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
