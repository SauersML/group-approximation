---
rg: 2
id: poly-growth-cantor-hosts-need-exponential-complexity-proof
kind: route
title: Feed polynomial ball growth and slow pattern counts into the ball-pattern growth bound, then apply Fekete, Gromov and Labbé's polynomial complexity
target: poly-growth-cantor-hosts-need-exponential-complexity
requires:
  - crossed-product-growth-bounded-by-ball-patterns
  - gromov-and-milnor-wolf-growth-alternatives
  - labbe-wang-shift-has-polynomial-pattern-complexity
---

Notation as in the target. `λ_X(N) = |L_(B_P(N))(X)|` is nondecreasing in `N`, because restriction
`L_(B_P(N'))(X) -> L_(B_P(N))(X)` is surjective for `N <= N'`.

**Step 0 (the bound).** By `crossed-product-growth-bounded-by-ball-patterns`, part 2, there are
`m, r` with `|B_G(n)| <= |B_P(mn)| · λ_X(mn + r)` for all `n`. Enlarging `m` keeps this true, since both
factors are nondecreasing, so assume `m >= 1`. For `n >= 1`,

`(★)  log |B_G(n)| <= log C + D log(mn) + log λ_X(mn + r)`.

**Part 1.** The sequence `|B_G(n)|` is submultiplicative, so by Fekete `ω_G = inf_n |B_G(n)|^(1/n)`, and
`log |B_G(n)| >= n log ω_G` for all `n`.

Suppose `β = liminf_N (log λ_X(N)) / N < (log ω_G) / m`, and fix `ε` with `β < ε < (log ω_G) / m`.
- There are `N_j -> ∞` with `log λ_X(N_j) <= ε N_j`.
- Put `n_j = ⌊(N_j - r) / m⌋`, so `m n_j + r <= N_j < m n_j + r + m`, and `λ_X(m n_j + r) <= λ_X(N_j)` by
  monotonicity.
- By (★), `n_j log ω_G <= log C + D log(m n_j) + ε (m n_j + r + m)`.
- Divide by `n_j -> ∞`. This gives `log ω_G <= ε m < log ω_G`, a contradiction.

So `liminf_N (log λ_X(N)) / N >= (log ω_G) / m`.
- If that `liminf` is `0`, no hosted `G` has `ω_G > 1`. That is, every hosted `G` has subexponential growth.
- The free group on two generators has `|B(n)| = 2·3^n - 1`, so `ω = 3 > 1`, and `k[F_2]` is not hosted.

**Part 2.** If `λ_X(N) <= C' N^E`, (★) gives `|B_G(n)| <= C C' m^D n^D (mn + r)^E`, a polynomial in `n`. By
`gromov-and-milnor-wolf-growth-alternatives`, part 1, `G` is virtually nilpotent.

**Part 3.** Take `P = Z^2` with generators `±e_1, ±e_2`, so `B_P(N)` is the `ℓ^1` ball, `|B_P(N)| <= (2N+1)^2`.
The ball `B_P(N)` lies in a `(2N+1) × (2N+1)` square. So every pattern on it is the restriction of a square
pattern of `Ω_U`, and `λ_(Ω_U)(N) <= p(2N + 1)`.
- By `labbe-wang-shift-has-polynomial-pattern-complexity`, `p(n) <= 50 · 4^9 · n^16`, so
  `λ_(Ω_U)(N) <= 50 · 4^9 · (2N + 1)^16`.
- Part 2 applies. Every `G` with `k[G] ↪ LC(Ω_U, k) ⋊ Z^2` is virtually nilpotent, and `F_2` is not virtually
  nilpotent.

**Part 4.** `crossed-product-growth-bounded-by-ball-patterns`, part 3, makes `k[G] -> B` injective
under the stated hypotheses. Then Parts 1 and 2 apply verbatim.

**General spaces.** The coefficients of the images of the generators live in `LC(Y, k) ⋊ P` for a subshift
factor `Y` (Remark in the growth-bound node), and the embedding of `k[G]` lands there. Apply the above to `Y`.
