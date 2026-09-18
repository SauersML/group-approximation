import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Trivial
import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Cube
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2BaseEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil gap over `ℤ[1/m]`: the case `m = 0` and the cube form

Lane `bh-met-44`.  Lane `bh-met-37` isolated `CharZeroK2NilGapStatement`: for every `m`, over
`A = ℤ[1/m]` (`Localization.Away (m : ℤ)`), (i) the one-variable nil part
`PolyK2OneVarNilStatementOver A` and (ii) diagonal injective stability on `ker ev₀` at rank
`k + 4`, `PolyK2StabRangeDiagStatementOver A 4`.

## Results

* `CharZeroK2CubeGapPosStatement`: for `m ≥ 1`, the cube form `PolyK2CubeNilStatementOver A`
  (module `ElemFPZInvK2Cube`) and `PolyK2StabRangeDiagStatementOver A 4`.
  **This is the isolated gap.**
* `charZeroK2NilGap_of_cubeGapPos`: the gap gives `CharZeroK2NilGapStatement`.  The case `m = 0`
  is proved (`charZeroK2NilGap_zero`: `ℤ[1/0]` is the zero ring).  For `m ≥ 1` the one-variable
  half comes from the cube form (`polyK2OneVarNilOver_of_cubeNil`: the cube reduction `nil_of_cube`
  of lane `bh-met-34`, used over `ℤ[1/m]`, and the passage `A[s_0..s_k] ≅ A[s_1..s_k][s_0]`).
* `charZeroK2CubeGapPos_of_nilGap`: the converse, so the gap is not logically stronger.
* `charZeroK2NilPos_of_cubeGapPos`, `charZeroStableK2FG_of_base_of_cubeGapPos`,
  `charZeroStableK2FG_of_basePos_of_cubeGapPos`: the gap wired into the chain, the last one
  with lane `bh-met-36`'s positive base gap `CharZeroK2BasePosFGStatement`.

## Why the target is not closed here

Both halves are deep theorems of algebraic `K`-theory, far beyond what the repository has.
(i) is Quillen's homotopy invariance `NK₂(R) = 0` for regular noetherian `R`, and even its first
case `K₂(ℤ[1/m][t]) = K₂(ℤ[1/m])` stably goes through the localization sequence.  (ii) needs
Bass's stable range bound `sr(ℤ[1/m][s_1..s_k]) ≤ k + 2` (not in Mathlib) and van der Kallen's
injective stability theorem for `K₂`, a long Steinberg-group word calculation.

## Truth check (offset `d = 4`)

`m = 0`: proved.  Let `m ≥ 1` and `S = ℤ[1/m][s_1..s_k]`, a regular noetherian ring of Krull
dimension `k + 1`, `k ≥ 1`.

*(i), cube form.*  An element killed by every `s_i ↦ 0` is killed by `ev₀ = ev₀ ∘ π_0`.  By
Quillen, `NK₂` of the regular ring `S` vanishes, so the stable image of an element of `ker ev₀`
is `0`, and since stable `K₂` is the filtered colimit of `K₂(n, S)`, the element dies at a finite
rank.  No rank bound is involved.  **True.**

*(ii) at `N = k + 4`.*  **Loud flag, confirmed: this is the boundary case, with no margin.**
Bass: `sr(S) ≤ dim S + 1 = k + 2`.  Van der Kallen (and Suslin–Tulenbaev): `K₂(n, R) → K₂(n + 1, R)`
is injective for `n ≥ sr(R) + 2` (Vaserstein's normalization, `sr(field) = 1`).  Sanity check of
the normalization: over a field it gives `n ≥ 3`, which is Matsumoto's `K₂(3, F) = K₂(F)`, and
`K₂(2, F) → K₂(3, F)` is not injective in general, so the bound cannot be lowered by one.  Here
`n = k + 4 = (k + 2) + 2` is covered exactly.  Dennis's bound `n ≥ dim Max(S) + 3 = k + 4` lands on
the same rank.  So **d = 4 is true**, and no rewiring to `d = 5` is needed.  The fallback at
`d = 5` stays available through `charZeroK2NilPosOffset_of_gap`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **The isolated gap** (lane `bh-met-44`): over every `ℤ[1/m]` with `m ≥ 1`, the cube form of
the nil part and diagonal injective stability on `ker ev₀` at rank `k + 4`. -/
def CharZeroK2CubeGapPosStatement : Prop :=
  ∀ m : ℕ, 0 < m →
    PolyK2CubeNilStatementOver (Localization.Away (m : ℤ)) ∧
      PolyK2StabRangeDiagStatementOver (Localization.Away (m : ℤ)) 4

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2CubeGapPosStatement

/-- **Endpoint (lane `bh-met-44`).**  The gap gives `CharZeroK2NilGapStatement`. -/
theorem charZeroK2NilGap_of_cubeGapPos (h : CharZeroK2CubeGapPosStatement) :
    CharZeroK2NilGapStatement := by
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact charZeroK2NilGap_zero
  · exact ⟨polyK2OneVarNilOver_of_cubeNil _ (h m hm).1, (h m hm).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilGap_of_cubeGapPos

/-- Conversely, `CharZeroK2NilGapStatement` gives the gap, so the gap is not logically stronger. -/
theorem charZeroK2CubeGapPos_of_nilGap (h : CharZeroK2NilGapStatement) :
    CharZeroK2CubeGapPosStatement :=
  fun m _ ↦ ⟨polyK2CubeNilOver_of_oneVar _ (h m).1, (h m).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2CubeGapPos_of_nilGap

/-- The gap gives vanishing of `ker ev₀` on `K₂(N, ℤ[1/m][t_0..t_{k-1}])`, `k ≥ 1`, `N ≥ k + 4`. -/
theorem charZeroK2NilPos_of_cubeGapPos (h : CharZeroK2CubeGapPosStatement) :
    CharZeroK2NilPosStatement :=
  charZeroK2NilPos_of_nilGap (charZeroK2NilGap_of_cubeGapPos h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilPos_of_cubeGapPos

/-- **Combined endpoint.**  The base part and the gap give `CharZeroStableK2FGStatement`. -/
theorem charZeroStableK2FG_of_base_of_cubeGapPos (hbase : CharZeroK2BaseFGStatement)
    (h : CharZeroK2CubeGapPosStatement) : CharZeroStableK2FGStatement :=
  charZeroStableK2FG_of_base_of_nilGap hbase (charZeroK2NilGap_of_cubeGapPos h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_base_of_cubeGapPos

/-- **Combined endpoint, both degenerate cases removed.**  Lane `bh-met-36`'s positive base gap
and the gap give `CharZeroStableK2FGStatement`. -/
theorem charZeroStableK2FG_of_basePos_of_cubeGapPos (hbase : CharZeroK2BasePosFGStatement)
    (h : CharZeroK2CubeGapPosStatement) : CharZeroStableK2FGStatement :=
  charZeroStableK2FG_of_base_of_cubeGapPos (charZeroK2BaseFG_of_pos hbase) h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_basePos_of_cubeGapPos

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
