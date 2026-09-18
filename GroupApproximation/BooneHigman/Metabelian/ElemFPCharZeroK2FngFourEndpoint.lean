import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngFourGroup
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(4, ℤ[1/m])` modulo a torus (lane `bh-met-92p`)

Target: `CZK2FngRankFourStatement` (`∀ m > 0`, `K₂(4, ℤ[1/m])` finitely normally generated in
`St_4(ℤ[1/m])`).  Not closed here.

**Residual.**  `czK2FngFour_TorusStatement`: for every `m > 0` there are finite sets
`S ⊆ K₂(4, ℤ[1/m])` and `T ⊆ St_4(ℤ[1/m])` such that the images of the elements of `T` in
`E_4(ℤ[1/m])` pairwise commute and `K₂(4, ℤ[1/m]) ≤ ⟪S⟫ ⊔ ⟨T⟩`.  The intended `T` is the finite
torus family `H_ab(v) = w_ab(v) w_ab(1)⁻¹` (`czStFourFP_H`) for `v ∈ {-1, m}` and `a ≠ b`,
whose images are the diagonal matrices `diag(…, v at a, …, v⁻¹ at b, …)`: the residual then
asks only that every element of `K₂` be, modulo finitely many normal generators, an element of
the torus subgroup.  All of `K₂ ∩ ⟨T⟩` (Steinberg symbols included) is then discharged by
`czK2FngFour_ker_fng_of_le_sup_closure`: `⟨T⟩` is finitely generated, its image is a finitely
generated commutative group, hence finitely presented, so `K₂ ∩ ⟨T⟩` is finitely normally
generated in `⟨T⟩` (Tietze with finitely generated source), and the Dedekind modular law
(`⟪S⟫ ⊴`, `⟪S⟫ ≤ K₂`) gives `K₂ = ⟪S ∪ (K₂ ∩ ⟨T⟩)-generators⟫`.

**LOUD: the residual is EQUIVALENT to the target as a Statement, not logically weaker.**
`czK2FngFour_torus_of_rankFour` takes `T = ∅`, and `czK2FngFour_rankFour_iff_torus` records the
equivalence.  It is strictly smaller only in proof content: a proof of the residual never has to
control the torus part `K₂ ∩ ⟨T⟩` (in particular it never has to know the symbol group
`K₂(ℤ[1/m])`, where the "symbols of `-1` and `p ∣ m`" route is false at `m = 5`).  No
finite-presentation hypothesis on `SL_4` or `E_4` enters; no literature input is used.

**Truth check.**  True, because it is equivalent to `CZK2FngRankFourStatement`, which is true
(`St_4(ℤ[1/m])` is finitely generated, proved in `czK2Fng_steinbergAway_fg`, and
`SL_4(ℤ[1/m])` is finitely presented by Behr's theorem; that citation is a truth check only).
The torus side condition was checked numerically for `m ∈ {2, 6, 10}`: the images of
`H_ab(v)`, `v ∈ {-1, m}` (`czStFourFP_u m`), are diagonal and pairwise commute.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **The residual (lane `bh-met-92p`).**  `K₂(4, ℤ[1/m])` is contained in `⟪S⟫ ⊔ ⟨T⟩` for a
finite `S ⊆ K₂` and a finite `T` with pairwise commuting images in `E_4(ℤ[1/m])`.
Equivalent to `CZK2FngRankFourStatement` (see the module docstring); smaller in proof content. -/
def czK2FngFour_TorusStatement : Prop :=
  ∀ m : ℕ, 0 < m → ∃ S T : Set (SteinbergGroup (Fin 4) (Localization.Away (m : ℤ))),
    S.Finite ∧ S ⊆ K2 (Fin 4) (Localization.Away (m : ℤ)) ∧ T.Finite ∧
    (∀ x ∈ T, ∀ y ∈ T, projection x * projection y = projection y * projection x) ∧
    K2 (Fin 4) (Localization.Away (m : ℤ)) ≤ Subgroup.normalClosure S ⊔ Subgroup.closure T

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_TorusStatement

/-- **The reduction.**  The torus residual gives `CZK2FngRankFourStatement`. -/
theorem czK2FngFour_rankFour_of_torus (h : czK2FngFour_TorusStatement) :
    CZK2FngRankFourStatement := by
  intro m hm
  obtain ⟨S, T, hS, hSK, hT, hcomm, hle⟩ := h m hm
  exact czK2FngFour_ker_fng_of_le_sup_closure
    (projection (I := Fin 4) (R := Localization.Away (m : ℤ))) S T hS hSK hT hcomm hle

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_rankFour_of_torus

/-- **LOUD converse** (`T = ∅`): the residual is not logically weaker than the target. -/
theorem czK2FngFour_torus_of_rankFour (h : CZK2FngRankFourStatement) :
    czK2FngFour_TorusStatement := by
  intro m hm
  obtain ⟨S, hS, hSK⟩ := h m hm
  refine ⟨S, ∅, hS, ?_, Set.finite_empty, ?_, ?_⟩
  · rw [← hSK]
    exact Subgroup.subset_normalClosure
  · intro x hx
    exact absurd hx (Set.notMem_empty x)
  · rw [← hSK]
    exact le_sup_left

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_torus_of_rankFour

/-- The residual and the target are equivalent as Statements. -/
theorem czK2FngFour_rankFour_iff_torus :
    CZK2FngRankFourStatement ↔ czK2FngFour_TorusStatement :=
  ⟨czK2FngFour_torus_of_rankFour, czK2FngFour_rankFour_of_torus⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_rankFour_iff_torus

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
