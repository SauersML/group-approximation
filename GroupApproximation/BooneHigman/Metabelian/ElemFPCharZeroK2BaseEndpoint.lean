import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2BaseTrivial
import GroupApproximation.Meta.AxiomGuard

/-!
# The base part `K₂(N, ℤ[1/m])`: the case `m = 0` and the positive gap

Lane `bh-met-36`.  `CharZeroK2BaseFGStatement` (module `ElemFPCharZeroK2Split`) asks that
`K₂(N, ℤ[1/m])` be finitely generated for all `m` and all `N ≥ 5`.

**Warning.**  `K₂(ℤ[1/m]) ≠ 0` for every `m ≥ 1`: the symbol `{-1,-1}` has real Hilbert symbol
`-1`.  Nothing here claims that a `K₂` vanishes.

## Results

* `charZeroK2Base_zero`: `m = 0` is proved.  `ℤ[1/0]` is the zero ring, so `St_N` is trivial.
* `CharZeroK2BasePosFGStatement`: the same statement for `m ≥ 1` only.
  **This is the isolated gap.**
* `charZeroK2BaseFG_of_pos`: the positive gap implies `CharZeroK2BaseFGStatement`.
* `charZeroK2BasePos_of_baseFG`: the converse.  The two are logically equivalent, and the reduction
  only removes the proved degenerate case.
* `charZeroK2IntFG_of_basePos`: the instance `m = 1` of the gap is exactly finite generation of
  `K₂(N, ℤ)`, via `ℤ[1/1] ≅ ℤ` (`k2_fg_localizationAway_iff_of_eq_one`).
* `charZeroStableK2FG_of_basePos_of_nil`: the positive gap together with the nil part gives
  `CharZeroStableK2FGStatement`.

## Truth check

For `m ≥ 1`, `ℤ[1/m]` is a Dedekind domain, so its Bass stable rank is at most `2`.  Stability
(van der Kallen; Suslin–Tulenbaev) gives `K₂(N, ℤ[1/m]) ≅ K₂(ℤ[1/m])` for `N ≥ 4`.  Tate's
localization sequence `0 → K₂(ℤ) → K₂(ℤ[1/m]) → ⊕_{p ∣ m} F_p^× → 0`, with `K₂(ℤ) = ℤ/2`
(Milnor), shows this group is finite.  So `CharZeroK2BasePosFGStatement` is **true**.

## Why the gap is strictly smaller, and the routes evaluated

`CharZeroK2BasePosFGStatement` drops the case `m = 0`, which is proved here.  It is the honest
arithmetic core.

* Route (a), `m = ±1`: the case `m = 1` reduces to `K₂(N, ℤ)` (proved transport).  Milnor's
  computation `K₂(N, ℤ) = ℤ/2` is a long word calculation and is not attempted.
* Route (b), localization: going from `ℤ` to `ℤ[1/m]` needs both `K₂(N, ℤ)` FG and a
  prime-by-prime localization step.  That is two hard inputs, so it is not taken as the gap.
* Route (c), the Steinberg presentation: `K₂` is finitely normally generated whenever `St_N` and
  `E_N` are finitely presented (Tietze), and central `K₂` then makes it finitely generated
  (`ElemFPCharZeroK2BaseCentral.k2_fg_of_le_center`).  But finite presentation of
  `E_N(ℤ[1/m])` is the `k = 0` instance of what lane `bh-met-17` reduces *to* `K₂` finite
  generation, so this route is circular.  It also needs full centrality of `K₂` in `St_N`, which
  the repository does not yet have.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Proved case `m = 0`.**  `K₂(N, ℤ[1/0])` is finitely generated, since `ℤ[1/0] = 0`. -/
theorem charZeroK2Base_zero (N : ℕ) :
    Group.FG (K2 (Fin N) (Localization.Away ((0 : ℕ) : ℤ))) :=
  k2_fg_localizationAway_of_eq_zero Nat.cast_zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2Base_zero

/-- **Gap (lane `bh-met-36`).**  For `m ≥ 1` and `N ≥ 5`, `K₂(N, ℤ[1/m])` is finitely generated.
It is true: the group is finite by stability and Tate's localization sequence (see the module
docstring).  It is `CharZeroK2BaseFGStatement` with the proved degenerate case `m = 0` removed. -/
def CharZeroK2BasePosFGStatement : Prop :=
  ∀ m N : ℕ, 0 < m → 5 ≤ N → Group.FG (K2 (Fin N) (Localization.Away (m : ℤ)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2BasePosFGStatement

/-- **Endpoint (lane `bh-met-36`).**  The positive gap implies `CharZeroK2BaseFGStatement`. -/
theorem charZeroK2BaseFG_of_pos (h : CharZeroK2BasePosFGStatement) :
    CharZeroK2BaseFGStatement := by
  intro m N h5N
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact charZeroK2Base_zero N
  · exact h m N hm h5N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2BaseFG_of_pos

/-- The positive gap is no stronger than `CharZeroK2BaseFGStatement`. -/
theorem charZeroK2BasePos_of_baseFG (h : CharZeroK2BaseFGStatement) :
    CharZeroK2BasePosFGStatement :=
  fun m N _ h5N ↦ h m N h5N

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2BasePos_of_baseFG

/-- Finite generation of `K₂(N, ℤ)` for `N ≥ 5`.  True: `K₂(N, ℤ) = ℤ/2` (Milnor). -/
def CharZeroK2IntFGStatement : Prop :=
  ∀ N : ℕ, 5 ≤ N → Group.FG (K2 (Fin N) ℤ)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2IntFGStatement

/-- The instance `m = 1` of the positive gap is finite generation of `K₂(N, ℤ)`. -/
theorem charZeroK2IntFG_of_basePos (h : CharZeroK2BasePosFGStatement) :
    CharZeroK2IntFGStatement := fun N h5N ↦
  (k2_fg_localizationAway_iff_of_eq_one (I := Fin N) (x := ((1 : ℕ) : ℤ)) Nat.cast_one).mp
    (h 1 N Nat.one_pos h5N)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2IntFG_of_basePos

/-- The positive base gap and the nil part together give `CharZeroStableK2FGStatement`. -/
theorem charZeroStableK2FG_of_basePos_of_nil (hb : CharZeroK2BasePosFGStatement)
    (hn : CharZeroK2NilFGPosStatement) : CharZeroStableK2FGStatement :=
  charZeroStableK2FG_of_splitGap ⟨charZeroK2BaseFG_of_pos hb, hn⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_basePos_of_nil

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
