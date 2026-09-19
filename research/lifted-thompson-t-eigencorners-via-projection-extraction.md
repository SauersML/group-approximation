---
rg: 2
id: lifted-thompson-t-eigencorners-via-projection-extraction
kind: route
title: Specialize commutant projection extraction to the central translation and diagonalize the approximate corners into an exact one
target: lifted-thompson-t-centre-has-commutant-eigencorners
requires:
  - commutant-projection-extraction
---

Let `rho : T̄ -> U(Q)`, `Q = prod_n M_(k_n) / (+)_n M_(k_n)`, with
`delta = ||rho(z) - 1|| > 0`, and put `B = rho(T̄)' ∩ Q`.

**Step 1 (approximate corners).**  Apply the contrapositive form of
`commutant-projection-extraction` with `H = T̄`, `Theta = rho` and
`eps = z`, which is central.  For each `j >= 1` it gives a nonzero projection
`q_j in B` and `lambda_j in sp(rho(z))` with `|lambda_j - 1| >= delta` and
`||(rho(z) - lambda_j) q_j|| <= 1/j`.  Passing to a subsequence, let
`lambda_j -> lambda`, so that `|lambda - 1| >= delta`.

**Step 2 (diagonal lemma: approximate to exact).**  `T̄` is finitely
generated, say by `s_1, ..., s_m`.  Fix unitary lifts `S_(i,n)` of the
`rho(s_i)`, and a lift `Z_n` of `rho(z)`.  Lift each `q_j` to projections
`Q_(j,n)`, as in (L2) of `central-eigencorners-die-over-full-radical-quotients-proof`.
Then for each `j`:
- `max_i ||[Q_(j,n), S_(i,n)]|| -> 0` as `n -> infinity`;
- `limsup_n ||(Z_n - lambda_j) Q_(j,n)|| <= 1/j`;
- `Q_(j,n) != 0` for infinitely many `n`, since `q_j != 0`.

Choose `n_1 < n_2 < ...` inductively with
- `Q_(j,n_j) != 0`,
- `max_i ||[Q_(j,n_j), S_(i,n_j)]|| <= 1/j`,
- `||(Z_(n_j) - lambda_j) Q_(j,n_j)|| <= 2/j`.

Put `P_n = Q_(j,n_j)` if `n = n_j`, and `P_n = 0` otherwise, and let
`P = [(P_n)]`.
- `P` is a projection, and it is nonzero because `||P_(n_j)|| = 1` for all
  `j`.
- `P` commutes with each `rho(s_i)`, hence with each `rho(s_i)^* = rho(s_i^(-1))`,
  hence with `rho(T̄)`.  So `P in B`.
- `||(Z_(n_j) - lambda) P_(n_j)|| <= 2/j + |lambda_j - lambda| -> 0`, so
  `rho(z) P = lambda P`, with `lambda != 1`.

This is (EC).  The same diagonal argument shows that the approximate form
stated in the target implies (EC).  The converse is trivial. ∎

**Scope.**  This route spends the full general claim, for every countable
`H` and every central `eps`.  The target needs only one pair.  Refuting
`commutant-projection-extraction` in general, for example by a Kazhdan source
as its node suspects, does not touch the target.
