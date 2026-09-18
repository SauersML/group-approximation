import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngEndpoint
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-four leaf `E_4(ℤ[1/m])` f.p., as Behr's statement for `SL_4(ℤ[1/m])` (bh-met-91a)

Chain: `CharZeroRankFourFPStatement` → `CZK2FngRankFourStatement`
(`czK2FngRankFour_of_rankFourFP`) → `CharZeroK2PosStabGenStatement`
(`czTriOff_posStabGen_of_rankFour`, TriOff closed).  So the root hypothesis `hgen` needs only
the leaf "`E_4(ℤ[1/m])` is finitely presented".

**Residual (one).**  `czRankFourFP_SLFourStatement`: for every `m ≥ 1`, the group
`SL_4(ℤ[1/m]) = Matrix.SpecialLinearGroup (Fin 4) (Localization.Away (m : ℤ))` is finitely
presented.  This is literally the `S`-arithmetic statement, with no Steinberg group, no `K₂`,
no elementary subgroup and no `MvPolynomial` wrapper.

**Proved here.**
* `czRankFourFP_slEquiv`: `SL_N(ℤ[1/m]) ≃* E_N(ℤ[1/m])` for every `N ≥ 1` and every `m`.
  Elementary matrices have determinant one (`Absorption.suslin_det_eq_one_of_mem_elementaryGroup`),
  and `SL_N = E_N` over `ℤ[1/m]` by the corpus Euclidean elimination
  (`Absorption.specialLinearInElementary_away`, no literature input).
* `czRankFourFP_elemFour_of_sl`, `czRankFourFP_k2FngRankFour_of_sl`,
  `czRankFourFP_posStabGen_of_sl`: the residual gives `E_4` f.p., then `CZK2FngRankFourStatement`
  (Tietze with the finitely generated source `St_4(ℤ[1/m])`), then `hgen`.
* `czRankFourFP_sl_of_rankFourFP`: `CharZeroRankFourFPStatement` implies the residual.
* `czRankFourFP_posStabGen_of_rankFourFP`: the requested wiring from the existing leaf.

**Strength (LOUD).**  The residual is implied by `CharZeroRankFourFPStatement`
(`czRankFourFP_sl_of_rankFourFP`).  The converse is not proved: it would also need the
degenerate instance `m = 0` (the zero ring, where `E_4` is trivial).  So the residual is
strictly weaker than `CharZeroRankFourFPStatement` only by that degenerate instance, and it is
strictly smaller in proof content only by `SL = E` over `ℤ[1/m]` and the empty-polynomial
transport.  Mathematically it still carries the whole depth of the rank-four leaf: Behr's
finite presentation of `SL_4(ℤ[1/m])`.  It is **not** closed here.

**Truth check.**  True.  `m = 1`: `SL_4(ℤ)` is finitely presented (Steinberg presentation with
`K₂(ℤ) = ℤ/2`).  `m > 1`: `SL_4(ℤ[1/m])` is an `S`-arithmetic group of a split simple group of
rank `3 ≥ 2`, so it is finitely presented (Behr; Borel–Serre).  These citations only justify
truth; none of them is a hypothesis anywhere in this file.

**Not used.**  `CZK2FngRankFourStatement` and `CharZeroK2PosStabGenStatement` appear only as
conclusions.  No unit-symbol route: the symbols `{u, v}` with `u, v ∈ ⟨-1, p | p ∣ m⟩` do not
generate `K₂(ℤ[1/m])` (for `m = 5` the tame symbol misses half of `F₅^×`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **`SL_N(ℤ[1/m]) ≃* E_N(ℤ[1/m])`** for `N ≥ 1`: the inclusion `SL_N → GL_N` lands in
`E_N` (Euclidean elimination), is injective, and hits every elementary matrix since those have
determinant one. -/
noncomputable def czRankFourFP_slEquiv (m : ℕ) {N : ℕ} (hN : 0 < N) :
    Matrix.SpecialLinearGroup (Fin N) (Localization.Away (m : ℤ)) ≃*
      elementaryGroup (Fin N) (Localization.Away (m : ℤ)) :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL).codRestrict
      (elementaryGroup (Fin N) (Localization.Away (m : ℤ))) fun g ↦
        Absorption.specialLinearInElementary_away m hN (Matrix.SpecialLinearGroup.toGL g) g.prop)
    ⟨fun _ _ hab ↦ Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hab), by
      rintro ⟨u, hu⟩
      exact ⟨⟨(u : Matrix (Fin N) (Fin N) (Localization.Away (m : ℤ))),
        Absorption.suslin_det_eq_one_of_mem_elementaryGroup hu⟩, Subtype.ext (Units.ext rfl)⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_slEquiv

/-- **The residual (lane `bh-met-91a`).**  `SL_4(ℤ[1/m])` is finitely presented for `m ≥ 1`.

True (Behr; Borel–Serre, truth only).  Implied by `CharZeroRankFourFPStatement`
(`czRankFourFP_sl_of_rankFourFP`); strictly weaker only by the degenerate `m = 0` instance, see
the module docstring.  Not an assumption of `CZK2FngRankFourStatement` or of `hgen` in any
form: it mentions neither `K₂` nor Steinberg groups. -/
def czRankFourFP_SLFourStatement : Prop :=
  ∀ m : ℕ, 0 < m →
    Group.IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin 4) (Localization.Away (m : ℤ)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_SLFourStatement

/-- The residual gives `E_4(ℤ[1/m])` finitely presented for `m ≥ 1`. -/
theorem czRankFourFP_elemFour_of_sl (h : czRankFourFP_SLFourStatement) (m : ℕ) (hm : 0 < m) :
    Group.IsFinitelyPresented (elementaryGroup (Fin 4) (Localization.Away (m : ℤ))) := by
  haveI := h m hm
  exact Group.IsFinitelyPresented.equiv (czRankFourFP_slEquiv m (N := 4) (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_elemFour_of_sl

/-- **Reduction.**  The residual gives `CZK2FngRankFourStatement`: `St_4(ℤ[1/m])` is finitely
generated and `E_4(ℤ[1/m])` is finitely presented, so the kernel `K₂(4, ℤ[1/m])` is finitely
normally generated. -/
theorem czRankFourFP_k2FngRankFour_of_sl (h : czRankFourFP_SLFourStatement) :
    CZK2FngRankFourStatement := by
  intro m hm
  haveI := czRankFourFP_elemFour_of_sl h m hm
  haveI := czK2Fng_steinbergAway_fg m 4 (by omega)
  exact czK2Fng_k2_of_fg_of_fp

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_k2FngRankFour_of_sl

/-- **Endpoint (gap `hgen` from the residual).** -/
theorem czRankFourFP_posStabGen_of_sl (h : czRankFourFP_SLFourStatement) :
    CharZeroK2PosStabGenStatement :=
  czTriOff_posStabGen_of_rankFour (czRankFourFP_k2FngRankFour_of_sl h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_posStabGen_of_sl

/-- The existing leaf `CharZeroRankFourFPStatement` implies the residual. -/
theorem czRankFourFP_sl_of_rankFourFP (h : CharZeroRankFourFPStatement) :
    czRankFourFP_SLFourStatement := by
  intro m hm
  haveI := czK2Fng_elemFour_fp_of_rankFourFP h m
  exact Group.IsFinitelyPresented.equiv (czRankFourFP_slEquiv m (N := 4) (by omega)).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_sl_of_rankFourFP

/-- **Endpoint (requested wiring).**  `hgen` from the existing leaf
`CharZeroRankFourFPStatement`. -/
theorem czRankFourFP_posStabGen_of_rankFourFP (h : CharZeroRankFourFPStatement) :
    CharZeroK2PosStabGenStatement :=
  czTriOff_posStabGen_of_rankFour (czK2FngRankFour_of_rankFourFP h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czRankFourFP_posStabGen_of_rankFourFP

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
