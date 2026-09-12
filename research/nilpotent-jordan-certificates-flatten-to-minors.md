---
rg: 2
id: nilpotent-jordan-certificates-flatten-to-minors
kind: claim
title: An idempotent certified below a nilpotent matrix of order k obeys the Jordan bound already in K_0
distinct_from:
  rank-functions-extending-a-state-are-pinned-on-regular-elements: that shows a state pins the rank of regular elements and leaves nilpotent data free in [0, 2/3] on F_3[C_3]; this shows the Jordan upper bound on nilpotents is forced by minors alone, so no single nilpotent can obstruct the upgrade.
  split-identity-minors-survive-triangular-moves: that removes split triangular steps from identity certificates; this removes the whole chain of Sylvester-nullity steps behind the Jordan bound, whose carried minors are not split.
artifacts:
  - research/artifacts/separated-triangular-certificates-flatten-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `nilpotent-jordan-certificates-flatten-proof`. Verification requested from
`w4-vf-linear-b`.

Let `A` be a unital ring, `u` an `n x n` matrix over `A` with `u^k = 0` for some `k >= 1`, and `f` an
idempotent matrix with `f <~ u` (that is, `f = L u R`). Then:
- `f^((+)j) <~ I_((j-1)n) (+) u^j` for `1 <= j <= k`, through minors only;
- in particular `f^((+)k) <~ I_((k-1)n)`;
- so `k [f] <= (k-1) n [A]` in `K_0(A)`, and every state `s` on `(K_0(A), [A])` has `s(f) <= (k-1) n/k`.

**Consequences.**
- **The (U1b) kill test is impossible.** A ring holding `u in M_4(W)` with `u^3 = 0` and
  `L u R = diag(1,1,1,0)` fails the rank condition, since `I_9 <~ f^((+)3) <~ I_8`. Weak finiteness is not
  needed. This settles the configuration recorded on `anti-central-weakly-finite-images-carry-rank-functions`.
- **Outer s-rank.** The outer s-rank `rho^s(X) = sup s([f])` over idempotents `f <~ X` obeys
  `rho^s(u) <= (k-1)n/k`. For characteristic-three root elements `g - 1`, the bound `2/3` that any
  Sylvester rank function imposes is already forced by `K_0`.
- **Where (U1b) can fail.** No single nilpotent can make the free Jordan data of Proposition B(4)
  inconsistent. An obstruction must use a triangular step that mixes blocks, which
  `separated-triangular-steps-flatten-to-minors` does not remove.

**Sharpness.** On `F_3[C_3]`, `x - 1` has cube zero and rank 2 of 3 in the regular representation. Over a
division ring the statement is the Jordan-form bound.

Proof: Section 2 of the artifact.
