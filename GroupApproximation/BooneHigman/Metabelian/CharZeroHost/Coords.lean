import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.BooneHigman.Coordinates.FGSubring
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Endpoint
import GroupApproximation.BooneHigman.Metabelian.ChainCharZero
import GroupApproximation.Meta.AxiomGuard

/-!
# Char-zero polynomial coordinates: the group layer (lane bh-met-09)

Research node `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`: a finitely
generated `H ≤ GL_n(K)`, `char K = 0`, embeds in `GL_M(ℤ[1/m][t_1, …, t_k])`.

**Route.**
1. `Coordinates.exists_finset_factor`: the inclusion `H ↪ GL_n(K)` factors through `GL_n(B)`,
   `B = Subring.closure t` for a finite set `t` of matrix entries (`factor_injective`).
2. The isolated ring statement `FGSubringCoordinatesStatement` gives `B ↪ M_N(ℤ[1/m][t])`.
3. `MatrixEmbedding.exists_injective_gl` passes to `GL`.
Endpoints: `coordinatesStatement_of_fgSubring`, and
`charZeroLinearHostStatement_of_fgSubring`, which feeds it together with
`charZeroAffineSelfSimilarStatement` into `Chain.charZeroLinearHostStatement_of_chain`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

/-- **Isolated ring statement** (strictly smaller than
`Chain.CharZeroPolynomialCoordinatesStatement`: it concerns a single finitely generated subring,
with no group layer).  Every finitely generated subring `B = ℤ[t]` of a char-zero field embeds in
a matrix ring over `ℤ[1/m][t_1, …, t_k]`.

Why it is true: `ℚ[B]` is a finitely generated `ℚ`-domain; Noether normalization gives a finite
injective `ℚ[x_1, …, x_s] → ℚ[B]`, and generic freeness a `g` with `ℚ[B][1/g]` free of rank `N`
over `ℚ[x][1/g]`, so `B ↪ M_N(ℚ[x][1/g])` by the regular representation.  As in characteristic
`p` (`CharPCoords.matrixEmbedding_localizationAway`, over any field) `ℚ[x][1/g] ↪ M(ℚ[x'])`.
The images of the finitely many generators of `B` have entries with finitely many denominators,
with product `m`; the matrices with entries in `ℤ[1/m][x'] ⊆ ℚ[x']` form a subring containing
them, so the embedding of `B` lands in `M(ℤ[1/m][x'])`. -/
def FGSubringCoordinatesStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (t : Finset K),
    ∃ m k : ℕ, Coordinates.MatrixEmbedding (Subring.closure (↑t : Set K)) (Chain.SIntPoly m k)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.FGSubringCoordinatesStatement

/-- **Reduction**: the ring statement implies the char-zero polynomial-coordinates node. -/
theorem coordinatesStatement_of_fgSubring
    (h : FGSubringCoordinatesStatement) : Chain.CharZeroPolynomialCoordinatesStatement := by
  intro K _ _ n H hH
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨t, ht⟩ := Coordinates.exists_finset_factor H.subtype
  obtain ⟨ρ', hρ'⟩ := ht (Subring.closure (↑t : Set K)) Subring.subset_closure
  have hρ'inj : Function.Injective ρ' := Coordinates.factor_injective hρ' H.subtype_injective
  obtain ⟨m, k, hemb⟩ := h K t
  obtain ⟨M, ψ, hψ⟩ := hemb.exists_injective_gl n
  exact ⟨m, k, M, ψ.comp ρ', hψ.comp hρ'inj⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.coordinatesStatement_of_fgSubring

/-- **Composition**: with the self-similar host proved (`charZeroAffineSelfSimilarStatement`),
the char-zero linear host node follows from the ring statement and the three remaining chain
leaves. -/
theorem charZeroLinearHostStatement_of_fgSubring (hcoord : FGSubringCoordinatesStatement)
    (habs : Chain.CharZeroElementaryAbsorptionStatement)
    (hfp : Chain.CharZeroElementaryFPStatement) (haff : Chain.AffineExtensionFPStatement) :
    Chain.CharZeroLinearHostStatement :=
  Chain.charZeroLinearHostStatement_of_chain
    (coordinatesStatement_of_fgSubring hcoord) habs hfp haff
    charZeroAffineSelfSimilarStatement

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.charZeroLinearHostStatement_of_fgSubring

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
