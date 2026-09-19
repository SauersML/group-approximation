# Route-A Z1-nil and P1: the exact rings, and whether an elementary proof reaches them (lane sk-k2-gersten, 2026-09-19)

Scope: the nil part of `ElemFPCharZero.CharZeroK2SplitGapStatement` (Z1-nil) and P1. Both are
`ElemFP.PolyK2NilGapStatementOver A d` (`ElemFPCharZeroK2NilGeneric`): the conjunction of
- `PolyK2OneVarNilStatementOver A`: for every `k` and every `N ≥ k+5`, the kernel of `t ↦ 0` on
  `K₂(N, A[s₁..s_k][t])` dies after padding, i.e. stable `NK₂(A[s₁..s_k]) = 0`;
- `PolyK2StabRangeDiagStatementOver A d`: injective stability on `ker ev₀` of `K₂(k+d, A[s₁..s_k])`,
  for `k ≥ 1`.

## Exact rings
- P1: `A = F_p`, so the rings are `F_p[s₁..s_k]` and `F_p[s₁..s_k][t]` for every `k`, with `d = 4`.
- Z1-nil: `A = ℤ[1/m]` for every `m`, so the rings are `ℤ[1/m][s₁..s_k][t]`, with the offset set in
  `ElemFPCharZeroK2NilEndpoint`. The number of variables `k` is unbounded along the route: it grows
  with the input group, so no fixed finite set of instances suffices.

## Does the weak algorithm plus Steinberg relations suffice? No.
- These rings are commutative polynomial rings in `≥ 1` (usually `≥ 2`) variables. They have no weak
  algorithm; that tool is for free associative algebras. They are not Euclidean except `F_p[t]`.
- Even the `K₁` analogue fails to be elementary. `SL_n(A[s]) = E_n(A[s])` for `n ≥ 3` is Suslin's
  theorem, which is route-A input S1 itself.
- The nil conjunct is homotopy invariance of `K₂` for regular rings (Quillen's fundamental theorem).
  For `A[s₁..s_k]` with `k ≥ 1` over `F_p`, and already for `k = 0` over `ℤ[1/m]` (`ℤ[1/m][t]` has
  dimension 2), I know no elementary Steinberg-group proof.
- The stability conjunct is van der Kallen's injective stability for `K₂` (Invent. Math. 1977) at
  `n ≥ sr + 2`, with Bass's bound `sr(A[s₁..s_k]) ≤ dim + 1`. This part IS elementary (Steinberg-group
  combinatorics), but it is a long formalization, and Mathlib has no stable-range theory.

## What is already formalized (the elementary part)
- The `k = 0` instance over `F_p` is on main, unconditionally:
  `bhNagaoUncond_wire_oneVarNilOver_zero_of_nagao`, from Nagao's `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`
  (`bhNagaoUncond_wire_K2_bot_nagao`, `ElemFPBhNagaoWireUncondBase`).
- The generic reductions over any commutative `A` are proved: `polyK2NilOver_of_oneVar` and
  `polyK2NilStabilityOver_of_diag`.
Nothing further at these instances is reachable by the weak-algorithm method.

## Recommendation for the owners (bh-pal-wire, sk-k2-loc)
The only elementary target left is van der Kallen stability, and that needs a stable-range library
first. The nil conjunct needs either Quillen-level K-theory in Lean, or a new elementary proof of
`NK₂ = 0` for `F_p[s₁..s_k]` and `ℤ[1/m][s₁..s_k]`, which would be a research result. The same wall
stops the SK row (`gq-sk-k2-gersten-feasibility.md`).
