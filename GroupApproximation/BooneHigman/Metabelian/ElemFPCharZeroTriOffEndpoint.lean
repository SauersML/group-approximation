import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffCore
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroStabGenTri
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import GroupApproximation.Meta.AxiomGuard

/-!
# `CZStabGenTriOffStatement`, proved outright (lane bh-met-90l)

Fix `m > 0`, `n ≥ 4`, and `i ≠ k` in `Fin n`.  Since `n ≥ 4`, there are two distinct
indices `j, j' ∉ {i, k}`.  The Tri word `T = Y_{e_i α + e_k δ} X_{e_i ζ + e_k η} Y_{e_i β}
X_{e_i γ}` avoids both `j.castSucc` and `j'.castSucc` (`czTriOff_T_mem`).  Over
`ℤ[1/m]`, `SL_{n-1} = E_{n-1}` holds by the Euclidean-division instance
`Absorption.specialLinearInElementary_away`, which is proved in the corpus with no
literature input.  So `czTriOff_core` gives the required `H X Y X Y H` word with `g₁ = 1`.

**Truth check.**  The Statement is true: this file proves it.  No residual Statement is left.
The only inputs are elementary matrix identities and `SL = E` over a Euclidean-type ring.
None of these avoided routes is used:

* the unit-symbol route;
* van der Kallen;
* p-power gluing;
* Witt/Greenberg or Cohen theory;
* any Higman route.

**Wiring.**  `czTriOff_posStabGen_of_rankFour` closes the gap `hgen`
(`CharZeroK2PosStabGenStatement`) from `CZK2FngRankFourStatement` alone.  It does so through
the existing reduction `czStabGen_posStabGen_of_rankFour_triOff`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- **Endpoint.**  The `K₂`-free residual `CZStabGenTriOffStatement` holds. -/
theorem czTriOff_triOffStatement : CZStabGenTriOffStatement := by
  intro m n _ hn i kk _ α δ ζ η β γ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 0 < k := by omega
  have hcard : 1 < (Finset.univ \ {i, kk} : Finset (Fin (k + 1))).card := by
    have h1 := Finset.card_le_card_sdiff_add_card (s := (Finset.univ : Finset (Fin (k + 1))))
      (t := {i, kk})
    have h2 := Finset.card_insert_le i ({kk} : Finset (Fin (k + 1)))
    rw [Finset.card_univ, Fintype.card_fin] at h1
    rw [Finset.card_singleton] at h2
    omega
  obtain ⟨j, hj, j', hj', hjj'⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hj hj'
  obtain ⟨hji, hjk⟩ := hj
  obtain ⟨hj'i, hj'k⟩ := hj'
  obtain ⟨g₂, v, w, c, w', hg₂, hv, hw, hc, hw', hproj⟩ :=
    czTriOff_core (Absorption.specialLinearInElementary_away m hk) hjj'
      (czTriOff_T_mem hji hjk α δ ζ η β γ) (czTriOff_T_mem hj'i hj'k α δ ζ η β γ)
  exact ⟨j, hji, hjk, 1, g₂, v, w, c, w', one_mem _, hg₂, hv, hw, hc, hw', hproj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_triOffStatement

/-- **Wiring (gap `hgen`).**  `CharZeroK2PosStabGenStatement` from the rank-four finite
normal generation input alone. -/
theorem czTriOff_posStabGen_of_rankFour (h4 : CZK2FngRankFourStatement) :
    CharZeroK2PosStabGenStatement :=
  czStabGen_posStabGen_of_rankFour_triOff h4 czTriOff_triOffStatement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_posStabGen_of_rankFour

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
