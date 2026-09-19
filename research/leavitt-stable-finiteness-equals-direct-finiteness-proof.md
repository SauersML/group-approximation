---
rg: 2
id: leavitt-stable-finiteness-equals-direct-finiteness-proof
kind: route
title: Pad to a two-power, push into the corner, add back the complement
target: leavitt-stable-finiteness-equals-direct-finiteness
requires: [leavitt-matrix-amplification-in-unit-group-algebra]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
---

## Direct proof

Stably finite implies directly finite by taking `n = 1`.  For the converse,
argue the contrapositive: assume `S` is not stably finite and produce a scalar
failure.

Fix `n >= 1` and `A, B` in `M_n(S)` with `B A = I_n` and `A B != I_n`.

**Pad.**  Choose `N = 2^k >= n` and set `A' = diag(A, I_(N-n))`,
`B' = diag(B, I_(N-n))` in `M_N(S)`.  Block multiplication gives
`B' A' = I_N`, and `A' B' = diag(AB, I_(N-n)) != I_N` because its leading
block is not `I_n`.

**Transport.**  Let `j_N : M_N(S) -> S` be the injective ring map of the
prerequisite, `E = j_N(I_N)`, an idempotent, and put `a = j_N(A')`,
`b = j_N(B')`.  Then `a, b in E S E`, and

    b a = j_N(B'A') = j_N(I_N) = E,
    a b = j_N(A'B') != E,

the inequality because `j_N` is injective.

**Unitize.**  Set `a^ = a + (1 - E)` and `b^ = b + (1 - E)`.  Since
`a = EaE` and `b = EbE`, every cross term vanishes:
`a(1-E) = (1-E)a = b(1-E) = (1-E)b = 0`.  Therefore

    b^ a^ = b a + (1-E)^2 = E + (1 - E) = 1,
    a^ b^ = a b + (1 - E).

If `a^ b^` were `1 = E + (1-E)`, then comparing the two components of the
direct sum `E S E (+) (1-E)S(1-E)` — which is legitimate because
`ab in ESE` — would give `ab = E`, contradiction.  So `b^ a^ = 1 != a^ b^`
and `S` is not directly finite.

## Two places this could go wrong and does not

**The padding.**  Padding is only valid because `j_N` exists for arbitrarily
large `N`, not merely for one; the induction in the prerequisite supplies
every two-power, which is cofinal in the sizes.

**The unitization.**  It needs `j_N` to be a *ring* map into `S` with
idempotent image identity, not merely an additive or module map — otherwise
`(1-E)` would not be orthogonal to `a` and `b` and the cross terms would
survive.  This is why the amplification is stated as a nonunital ring
embedding rather than as an isomorphism onto a corner: the corner's identity
`E` is what makes the complement available.
