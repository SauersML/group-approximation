---
rg: 2
id: commuting-jordan-certificates-flatten-to-minors
kind: claim
title: If x commutes with P and x^m = 0, then m copies of an idempotent minor of xP are a minor of m-1 copies of P
distinct_from:
  nilpotent-jordan-certificates-flatten-to-minors: that is the case P = I, bounded by identity matrices; this allows any commuting P, the form the descent upper bound uses.
  separated-triangular-steps-flatten-to-minors: that removes one separated triangular step; this applies it m-1 times, to the Frobenius matrices of a commuting nilpotent.
artifacts:
  - research/artifacts/two-root-certificates-separate-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w6-upg-separate`, 2026-09-12; verification requested from `w4-vf-linear-b`).

Let `A` be a unital ring, `<~` the minor order `M = XNY`, and `x`, `P` square matrices with `xP = Px` and
`x^m = 0`. If `f` is an idempotent matrix with `f <~ xP`, then

    f^((+)j) <~ P^((+)(j-1)) (+) x^j P   for 1 <= j <= m,   so   f^((+)m) <~ P^((+)(m-1)).

**`K_0` reading.** For a state `s` on `(K_0(A), [A])`, put `rho^s(M) = sup s[f]` over idempotent minors
`f <~ M`, and `rho_s(M) = inf s[e]` over idempotents `e` with `M <~ e`. Then `rho^s(xP) <= (1 - 1/m) rho_s(P)`.

- **Instances.** `P = I_n` gives `nilpotent-jordan-certificates-flatten-to-minors`. With `x = N^B_12`,
  `P = P_k` and `m = 3` it is the idempotent-minor form of the descent upper bound `f(k+1) <= (2/3) f(k)`
  (Theorem 3.1.1 of `research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md`).
- **Limit.** The value form `d(xP) <= (1 - 1/m) d(P)` is not a matrix-state fact. On `F_3[u]/(u^3)` the matrix
  state `d(M) = dim soc(Im M)` has `d(u) = 1` (artifact Example 3.3).

Proof: `commuting-jordan-certificates-flatten-proof`.
