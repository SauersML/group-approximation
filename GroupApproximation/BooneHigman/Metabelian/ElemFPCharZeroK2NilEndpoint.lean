import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2NilTelescope
import GroupApproximation.Meta.AxiomGuard

/-!
# The nil part of `K₂(N, ℤ[1/m][t_0..t_{k-1}])`: reduction to one variable and the diagonal rank

Lane `bh-met-37`.  Lane `bh-met-28` (`ElemFPCharZeroK2Split`) isolated `CharZeroK2NilPosStatement`:
for `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element `u ∈ K₂(N, ℤ[1/m][t_0..t_{k-1}])` with `ev₀ u = 1`
is trivial.  This module replays the char-`p` reductions over the base ring `A = ℤ[1/m]`
(`Localization.Away (m : ℤ)`), through the ring-generic statements of `ElemFPCharZeroK2NilGeneric`.

* `CharZeroK2NilGapStatement`: for every `m`, the gap pair `PolyK2NilGapStatementOver A 4`, i.e.
  (i) the one-variable nil part over `A[s_1..s_k]` for `N ≥ k + 5`: an element of `K₂(N, A[σ][t])`
  killed by `t ↦ 0` dies at some finite rank; and (ii) diagonal injective stability on `ker ev₀`
  at `N = k + 4`, `k ≥ 1`.  **This is the isolated gap.**
* `charZeroK2NilPos_of_nilGap`: the gap gives `CharZeroK2NilPosStatement`.  The proof content is
  the induction on the number of variables (`polyK2NilOver_of_oneVar`), the passage to all ranks
  (`polyK2NilStabilityOver_of_diag`) and the telescoping on `ker ev₀`
  (`eq_one_of_K2IndexMap_eq_one_of_nilStab`).
* `charZeroK2NilGap_of_nilPos`: the converse.  So the gap is not logically stronger than
  `CharZeroK2NilPosStatement`.  It is strictly smaller in proof content.
* `charZeroStableK2FG_of_base_of_nilGap`: the base part and the gap give
  `CharZeroStableK2FGStatement`.
* `charZeroK2NilPosOffset_of_gap`: the same reduction at any offset `d ≥ 4`, for the fallback
  below.

The char-`p` specialization of the same statement form is in `ElemFPCharZeroK2NilCharP`.

## Truth check

If `m = 0`, `A` is the zero ring and every statement holds trivially.  Let `m ≥ 1` and
`S = A[s_1..s_k]`.

*(i) One-variable nil part.*  `S` is regular noetherian.  By Quillen's fundamental theorem,
`K₂(S[t]) → K₂(S)` is an isomorphism stably, so its kernel `NK₂(S)` is `0`.  Stable `K₂` is the
filtered colimit of the unstable `K₂(n, -)`.  So an unstable element whose stable image is `0` dies
at some finite rank.  No rank bound is involved, so the bound `N ≥ k + 5` is harmless.

*(ii) Diagonal stability at `N = k + 4`.*  **Loud flag: this is an edge case, with no margin.**
`S` has Krull dimension `k + 1` (and so does its maximal spectrum).  Bass's theorem gives
`sr(S) ≤ k + 2`, and this is not better in general: `sr(ℤ[t]) = 3`.  Injective stability for `K₂`
(van der Kallen 1977; Suslin–Tulenbaev 1976) says `K₂(n, R) → K₂(n + 1, R)` is injective for
`n ≥ sr(R) + 2`.  At `n = k + 4 = sr + 2` this is exactly the boundary case.  Dennis's older bound
`n ≥ dim Max(R) + 3 = k + 4` also lands on the boundary.  Both theorems cover the boundary, so the
statement is true; but in char `p` the same rank had one step of margin (`sr(F_p[σ]) ≤ k + 1`), and
here it has none.  Restricting to `ker ev₀` only weakens the claim.

*Fallback.*  If only `n ≥ sr + 3` is trusted, use offset `d = 5`: `charZeroK2NilPosOffset_of_gap`
gives vanishing of `ker ev₀` for `N ≥ k + 5` from `PolyK2NilGapStatementOver A 5`, which is safe.
The single rank `N = k + 4` would then stay open.  For the finite-generation chain one would
isolate only the finite generation of `ker ev₀` at `N = k + 4` (the FG form
`CharZeroK2NilFGPosStatement` restricted to that rank) as the remaining piece.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **The isolated gap** (lane `bh-met-37`): over every `ℤ[1/m]`, the one-variable nil part and
diagonal injective stability on `ker ev₀` at rank `k + 4`. -/
def CharZeroK2NilGapStatement : Prop :=
  ∀ m : ℕ, PolyK2NilGapStatementOver (Localization.Away (m : ℤ)) 4

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.CharZeroK2NilGapStatement

/-- `CharZeroK2NilPosStatement` is the generic vanishing statement at offset `4` over every
`ℤ[1/m]` (the hypothesis `N ≥ 5` is implied by `k ≥ 1` and `N ≥ k + 4`). -/
theorem charZeroK2NilPos_iff_forall_over :
    CharZeroK2NilPosStatement ↔
      ∀ m : ℕ, PolyK2NilPosStatementOver (Localization.Away (m : ℤ)) 4 :=
  ⟨fun h m k N hk hkN u hu ↦ h m k N hk hkN (by omega) u hu,
    fun h m k N hk hkN _ u hu ↦ h m k N hk hkN u hu⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilPos_iff_forall_over

/-- **Endpoint (lane `bh-met-37`).**  The gap gives `CharZeroK2NilPosStatement`. -/
theorem charZeroK2NilPos_of_nilGap (h : CharZeroK2NilGapStatement) :
    CharZeroK2NilPosStatement :=
  charZeroK2NilPos_iff_forall_over.mpr fun m ↦ polyK2NilPosOver_of_gap _ le_rfl (h m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilPos_of_nilGap

/-- Conversely, `CharZeroK2NilPosStatement` gives the gap, so the gap is not logically stronger. -/
theorem charZeroK2NilGap_of_nilPos (h : CharZeroK2NilPosStatement) :
    CharZeroK2NilGapStatement :=
  fun m ↦ polyK2NilGapOver_of_nilPos _ (charZeroK2NilPos_iff_forall_over.mp h m)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilGap_of_nilPos

/-- The gap gives finite generation of the nil part. -/
theorem charZeroK2NilFGPos_of_nilGap (h : CharZeroK2NilGapStatement) :
    CharZeroK2NilFGPosStatement :=
  charZeroK2NilFGPos_of_nilPos (charZeroK2NilPos_of_nilGap h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilFGPos_of_nilGap

/-- **Combined endpoint.**  The base part and the gap give `CharZeroStableK2FGStatement`. -/
theorem charZeroStableK2FG_of_base_of_nilGap (hbase : CharZeroK2BaseFGStatement)
    (hnil : CharZeroK2NilGapStatement) : CharZeroStableK2FGStatement :=
  charZeroStableK2FG_of_splitGap ⟨hbase, charZeroK2NilFGPos_of_nilGap hnil⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroStableK2FG_of_base_of_nilGap

/-- **Fallback form**, at any offset `d ≥ 4`: the gap pair at offset `d` over every `ℤ[1/m]`
gives vanishing of `ker ev₀` on `K₂(N, ℤ[1/m][t_0..t_{k-1}])` for `k ≥ 1`, `N ≥ k + d`.  At
`d = 5` the stability input has one step of margin over van der Kallen's bound. -/
theorem charZeroK2NilPosOffset_of_gap {d : ℕ} (hd : 4 ≤ d)
    (h : ∀ m : ℕ, PolyK2NilGapStatementOver (Localization.Away (m : ℤ)) d) :
    ∀ m : ℕ, PolyK2NilPosStatementOver (Localization.Away (m : ℤ)) d :=
  fun m ↦ polyK2NilPosOver_of_gap _ hd (h m)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.charZeroK2NilPosOffset_of_gap

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
