import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCoset
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The row-extension gap as injectivity of the parabolic map

Lane `bh-met-62`.  Modules `ElemFPK2VdKRowTransport`, `ElemFPK2VdKRowCanonical` and
`ElemFPK2VdKRowCoset` build van der Kallen row data unconditionally from one input: injectivity
of the canonical map `vdkRowPar : R^n × St_n(R) → St_{n+1}(R)`,
`(v, g) ↦ (∏ᵢ x_{i,last}(vᵢ)) · stab g`.

* `VdKRowParInjectiveStatement`: for every prime `p` and `k > 0`, `vdkRowPar` is injective at
  rank `k + 4` over `F_p[s_1, …, s_k]`.
* `vdkRowExtension_of_vdkRowParInjective`: this implies `VdKRowExtensionStatement`, with
  `X = P̃ \ St_{k+5}`.  `polynomialFpK2Vanishing_of_vdkRowParInjective` chains it to the
  endpoint.
* `K2Stab_eq_one_of_vdkRowPar_injective`: over any ring, injectivity of `vdkRowPar` gives
  injectivity of `K₂(n, R) → K₂(n+1, R)`.
* `stab_injective_of_vdkRowPar_injective`: it also gives injectivity of `stab` on all of `St_n(R)`.

**LOUD: the new statement is logically equivalent, not weaker.**  At each rank, injectivity of
`vdkRowPar` is equivalent to injectivity of `stab : St_n(R) → St_{n+1}(R)`.  That in turn is
equivalent to injectivity of `K₂(n, R) → K₂(n+1, R)`, because `ker stab ≤ K₂` and `stab` maps
`K₂` into `K₂`.  One direction is `stab_injective_of_vdkRowPar_injective`.  The other is
informal and not formalized here:

* the matrix of `vdkRowPar (v, g)` is `[[M_g, v], [0, 1]]`, so equal images force `v = v'` and
  `M_g = M_{g'}`;
* cancelling `colVec v` gives `stab g = stab g'`.

So the statement is equivalent to `VdKRowExtensionStatement` (the converse being
`VdKRowData.eq_one_of_K2Stab`) and to injective `K₂` stability at rank `k + 4`.  It is strictly
smaller in *proof content*: the permutations `Trow`, all five row relator families, the coset
bijection and the transport are now proved, and only injectivity of one explicit map remains.

Truth.  By Bass, `sr(F_p[s_1, …, s_k]) ≤ k + 1`.  Van der Kallen's injective stability gives
`K₂(n) → K₂(n+1)` injective for `n ≥ sr + 2`, which covers `n = k + 4`.  By the argument above,
`vdkRowPar` is then injective, so the statement is true.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- Over any ring, injectivity of the parabolic map gives injectivity of `K₂(n) → K₂(n+1)`. -/
theorem K2Stab_eq_one_of_vdkRowPar_injective {R : Type*} [Ring R] {n : ℕ}
    (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) (u : K2n n R)
    (hu : K2Stab n R u = 1) : u = 1 :=
  (vdkRowDataOfInjective hinj).eq_one_of_K2Stab
    (Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) 1) u hu

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Stab_eq_one_of_vdkRowPar_injective

/-- Injectivity of the parabolic map restricts to injectivity of `stab`. -/
theorem stab_injective_of_vdkRowPar_injective {R : Type*} [Ring R] {n : ℕ}
    (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) :
    Function.Injective (stab n R) := by
  intro g g' h
  have hp : vdkRowPar ((0 : Fin n → R), g) = vdkRowPar ((0 : Fin n → R), g') := by
    rw [vdkRowPar_apply, vdkRowPar_apply, h]
  exact (Prod.mk.inj (hinj hp)).2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.stab_injective_of_vdkRowPar_injective

/-- **The remaining gap**: the canonical map `P̃ → St_{k+5}(F_p[s_1, …, s_k])` is injective at
rank `k + 4`.  LOUD: logically equivalent to `VdKRowExtensionStatement` and to injective `K₂`
stability at rank `k + 4` (see the module docstring), with a strictly smaller proof content. -/
def VdKRowParInjectiveStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
    Function.Injective (vdkRowPar (n := k + 4) (R := MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowParInjectiveStatement

/-- Injectivity of the parabolic map gives the row-extension input. -/
theorem vdkRowExtension_of_vdkRowParInjective (h : VdKRowParInjectiveStatement) :
    VdKRowExtensionStatement := by
  intro p hp k hk
  exact ⟨VdKRowCoset (k + 4) (MvPolynomial (Fin k) (ZMod p)),
    ⟨Quotient.mk (QuotientGroup.rightRel
      (vdkRowParSubgroup (k + 4) (MvPolynomial (Fin k) (ZMod p)))) 1⟩,
    ⟨vdkRowDataOfInjective (h p hp k hk)⟩⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExtension_of_vdkRowParInjective

/-- Injectivity of the parabolic map gives the diagonal stable-range statement. -/
theorem polyK2StabRangeDiag_of_vdkRowParInjective (h : VdKRowParInjectiveStatement) :
    PolyK2StabRangeDiagStatement :=
  polyK2StabRangeDiag_of_vdkRowExtension (vdkRowExtension_of_vdkRowParInjective h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2StabRangeDiag_of_vdkRowParInjective

/-- Injectivity of the parabolic map, with the nilpotent and field inputs, gives polynomial `K₂`
vanishing over `F_p`. -/
theorem polynomialFpK2Vanishing_of_vdkRowParInjective (h : VdKRowParInjectiveStatement)
    (hnil : PolyK2NilPosStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_vdkRowExtension (vdkRowExtension_of_vdkRowParInjective h) hnil
    hfield

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_vdkRowParInjective

end GroupApproximation.BooneHigman.Metabelian.ElemFP
