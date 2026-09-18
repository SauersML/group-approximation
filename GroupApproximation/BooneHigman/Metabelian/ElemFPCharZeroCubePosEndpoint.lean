import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroCubePosStab
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeResidueFieldGap
import GroupApproximation.Meta.AxiomGuard

/-!
# The char-zero cube gap with both halves reduced

Lane `bh-met-90e`, endpoint module.  The root hypothesis `hcube : CharZeroK2CubeGapPosStatement`
says, over every `A = ℤ[1/m]`, `m ≥ 1`:

* (cube half) `PolyK2CubeNilStatementOver A`; lanes `bh-met-73c`, `bh-met-74`, `bh-met-81` cut it
  to `CZCubeResFieldStatement` (Quillen's `NK₂ = 0`, locally at `𝔪 ∋ p`, minimal rank);
* (diagonal half) `PolyK2StabRangeDiagStatementOver A 4`; module `ElemFPCharZeroCubePosStab`
  cuts it to `CZCubePosStabOverStatement A` (van der Kallen injective stability, only on the cube
  part `⋂ᵢ ker (s_i ↦ 0)`).

* `CZCubePosStatement`: the conjunction of the two reduced halves.  **The isolated gap.**
* `czCubePos_charZeroK2CubeGapPos_of_cubePos`: **endpoint**, it gives `hcube`.
* `czCubePos_charZeroK2CubeGapPos_of_resField_of_cubeStab`: the same, halves separate.
* `czCubePos_cubePos_of_charZeroK2CubeGapPos`: the converse.

## Strength (LOUD)

`CZCubePosStatement` is **logically equivalent** to `CharZeroK2CubeGapPosStatement` (both
directions are proved below).  No strictly weaker *logical* form exists for any statement `S` with
`S → hcube` proved, since then `S` is at least as strong as `hcube`.  It is **strictly smaller in
proof content**: relative to `CZCubeResFieldStatement ∧ diagonal half` (the state after lane
`bh-met-81`), the diagonal half now only has to be shown for elements killed by every
`s_i ↦ 0`; the cube decomposition that extends it to all of `ker ev₀` is proved here.

## Truth check

Both halves are true: the cube half by Quillen (`NK₂ = 0` for the regular ring
`ℤ[1/m][s_1..s_k]`), the diagonal half by Bass (`sr ≤ k + 2`, Krull dimension `k + 1`) and van der
Kallen (`K₂(n, S) ↪ K₂(n + 1, S)` for `n ≥ sr(S) + 2`, here `n = k + 4`).  The stability half is a
sub-family of the true diagonal half.  The target itself is not proved here: it is Quillen plus van
der Kallen, neither of which is in the repository.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **The isolated gap** (lane `bh-met-90e`): the minimal-rank local cube gap of lane `bh-met-81`,
and injective stability at rank `k + 4` on the cube part over every `ℤ[1/m]`, `m ≥ 1`.  LOUD:
logically equivalent to `CharZeroK2CubeGapPosStatement`, strictly smaller in proof content. -/
def CZCubePosStatement : Prop :=
  CZCubeResFieldStatement ∧
    ∀ m : ℕ, 0 < m → CZCubePosStabOverStatement (Localization.Away (m : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CZCubePosStatement

/-- **Endpoint, halves separate.**  The minimal-rank cube gap and cube-part stability give the
root hypothesis `CharZeroK2CubeGapPosStatement`. -/
theorem czCubePos_charZeroK2CubeGapPos_of_resField_of_cubeStab (h : CZCubeResFieldStatement)
    (hstab : ∀ m : ℕ, 0 < m → CZCubePosStabOverStatement (Localization.Away (m : ℤ))) :
    CharZeroK2CubeGapPosStatement :=
  czCubeResField_charZeroK2CubeGapPos_of_resField h fun m hm ↦
    czCubePos_stabRangeDiagOver_of_cubeStab _ (hstab m hm)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_charZeroK2CubeGapPos_of_resField_of_cubeStab

/-- **Endpoint (lane `bh-met-90e`).**  `CZCubePosStatement → CharZeroK2CubeGapPosStatement`. -/
theorem czCubePos_charZeroK2CubeGapPos_of_cubePos (h : CZCubePosStatement) :
    CharZeroK2CubeGapPosStatement :=
  czCubePos_charZeroK2CubeGapPos_of_resField_of_cubeStab h.1 h.2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_charZeroK2CubeGapPos_of_cubePos

/-- Conversely, `CharZeroK2CubeGapPosStatement` gives `CZCubePosStatement`. -/
theorem czCubePos_cubePos_of_charZeroK2CubeGapPos (h : CharZeroK2CubeGapPosStatement) :
    CZCubePosStatement :=
  ⟨czCubeResField_resField_of_residue
      (czCubeLocal_residue_of_gapLocal (czCubeGapLocal_of_charZeroK2CubeGapPos h)),
    fun m hm ↦ czCubePos_cubeStab_of_stabRangeDiagOver _ (h m hm).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czCubePos_cubePos_of_charZeroK2CubeGapPos

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
