import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Adjoin.FG
import GroupApproximation.BooneHigman.Coordinates.MatrixEmbedding
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Coords
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFree
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsAway
import GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators
import GroupApproximation.Meta.AxiomGuard

/-!
# Polynomial coordinates in characteristic zero: the ring statement (lane bh-met-30)

Research node `char-zero-linear-groups-embed-in-polynomial-s-integer-groups`, the isolated ring
statement `CharZeroHost.FGSubringCoordinatesStatement`:

  "`ℚ[B]` is a finitely generated `ℚ`-domain; Noether normalization gives a finite injective
  `ℚ[x_1, …, x_s] → ℚ[B]`, and generic freeness a `g` with `ℚ[B][1/g]` free ... so
  `B ↪ M_N(ℚ[x][1/g])` ... `ℚ[x][1/g] ↪ M(ℚ[x'])`.  The images of the finitely many generators
  of `B` have entries with finitely many denominators, with product `m` ... so the embedding of
  `B` lands in `M(ℤ[1/m][x'])`."

**Endpoints.** `fgSubringCoordinates : FGSubringCoordinatesStatement` and
`charZeroPolynomialCoordinates : Chain.CharZeroPolynomialCoordinatesStatement`.

**Route.**
1. `A = Algebra.adjoin ℚ t ⊆ K` (`DivisionRing.toRatAlgebra`) contains `B = Subring.closure t`
   and is a finitely generated `ℚ`-domain.
2. Noether normalization (`exists_finite_inj_algHom_of_fg`) and the char-`p` files, which work
   over any field: `CharPCoords.finiteDomainAwayEmbedding` gives `A ↪ M(P[1/f])`,
   `CharPCoords.matrixEmbedding_localizationAway` gives `P[1/f] ↪ M(P)`, `P = ℚ[x_0..x_{s-1}]`.
3. Restrict to `B` and clear denominators (`exists_matrixEmbedding_away_of_closure`).
-/

open GroupApproximation.BooneHigman.Coordinates

namespace GroupApproximation.BooneHigman.Metabelian.CharZeroHost

/-- **The isolated ring statement, proved.**  Every finitely generated subring of a char-zero
field embeds in a matrix ring over `ℤ[1/m][x_0, …, x_{k-1}]`. -/
theorem fgSubringCoordinates : FGSubringCoordinatesStatement := by
  intro K _ _ t
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra ℚ K, A = Algebra.adjoin ℚ (↑t : Set K) := ⟨_, rfl⟩
  have hle : Subring.closure (↑t : Set K) ≤ A.toSubring := by
    rw [Subring.closure_le, Subalgebra.coe_toSubring, hA]
    exact Algebra.subset_adjoin
  haveI : Algebra.FiniteType ℚ A :=
    (Subalgebra.fg_iff_finiteType A).mp (by
      rw [hA]
      exact Algebra.fg_adjoin_finset t)
  obtain ⟨s, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg ℚ A
  obtain ⟨f, hf⟩ := CharPCoords.finiteDomainAwayEmbedding ℚ s A g.toRingHom hginj hgfin
  obtain ⟨N, Φ, hΦ⟩ := hf.trans (CharPCoords.matrixEmbedding_localizationAway f)
  let ι : ↥(Subring.closure (↑t : Set K)) →+* ↥A :=
    { toFun := fun x => ⟨x.1, Subalgebra.mem_toSubring.1 (hle x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hι : Function.Injective ι := fun _ _ hxy =>
    Subtype.ext (congrArg Subtype.val hxy)
  obtain ⟨m, hm⟩ := exists_matrixEmbedding_away_of_closure t (Φ.comp ι) (hΦ.comp hι)
  exact ⟨m, s, hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.fgSubringCoordinates

/-- **Char-zero polynomial coordinates**, unconditionally: a finitely generated subgroup of
`GL_n(K)`, `char K = 0`, embeds in `GL_M(ℤ[1/m][x_0, …, x_{k-1}])`. -/
theorem charZeroPolynomialCoordinates : Chain.CharZeroPolynomialCoordinatesStatement :=
  coordinatesStatement_of_fgSubring fgSubringCoordinates

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.CharZeroHost.charZeroPolynomialCoordinates

end GroupApproximation.BooneHigman.Metabelian.CharZeroHost
