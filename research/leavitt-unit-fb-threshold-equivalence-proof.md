---
rg: 2
id: leavitt-unit-fb-threshold-equivalence-proof
kind: route
title: Select one good block per level with a pair-dependent Markov budget; the converse is a single-block model
target: leavitt-unit-frobenius-bounded-threshold-iff-fb-rigidity
requires:
  - leavitt-units-admit-no-bounded-block-monomial-hs-model
  - binary-leavitt-all-ranks-full-mf-radical
---

Notation as in `leavitt-unit-bounded-block-triviality-via-mf-radical`:
`rho_m(g)(e_x ⊗ v) = e_(sigma_g(x)) ⊗ u_m(g, sigma_g(x)) v`, `||X||_(2,k)^2 = (1/k) Tr(X^* X)`,
`||X||_F^2 = Tr(X^* X)`, and `||X||_op <= ||X||_F <= sqrt(k) ||X||_op`.

## (B) implies (A)

Let `rho_m` satisfy (BB') and suppose `||rho_m(s) - 1||_2^2 >= c > 0` along a
subsequence, for some `s in U`.

**(0) Frozen skeleton.**  (BB') includes `eps_m -> 0`, so `rho_m` is a
Hilbert--Schmidt asymptotic homomorphism into the block-monomial groups.  By
clause 1 of `leavitt-units-admit-no-bounded-block-monomial-hs-model`, every
`omega`-limit of `mu_m(g) := d_H(sigma_(m,g), id)` is `0`, hence `mu_m(g) -> 0`
for every `g`.

**(1) A persistent label in 2-norm.**  The column of `rho_m(s) - 1` at `x` is
`e_x ⊗ (u_m(s,x) - 1)` when `sigma_s x = x`, and has squared normalized norm at
most `4/n_m` otherwise.  Hence

```text
c <= (1/n_m) sum_(sigma_s x = x) ||u_m(s,x) - 1||_(2,k_m)^2 + 4 mu_m(s).
```

Once `mu_m(s) <= c/8`, the average on the right is at least `c/2`, and each term
is at most `4`.  So the set `B_m = {x : sigma_s x = x, ||u_m(s,x) - 1||_(2,k_m)^2 >= c/4}`
has density at least `c/16`.

**(2) Pair-dependent Markov budgets.**  Enumerate the pairs `(g_i, h_i)` of `U`,
put `C_i = sup_m k_m eps_m(g_i,h_i)^2 < infinity` and `M_i = 2^(i+7)/c`.  Let
`F_m(i)` be the set of blocks fixed by `sigma_(g_i)`, `sigma_(h_i)` and
`sigma_(g_i h_i)`, and for `x in F_m(i)` put
`delta_x(i) = ||u_m(g_i h_i, x) - u_m(g_i, x) u_m(h_i, x)||_(2,k_m)`.  Summing the
columns at fixed blocks, exactly as in step (1) of
`leavitt-unit-bounded-block-triviality-via-mf-radical`,

```text
(1/n_m) sum_(x in F_m(i)) delta_x(i)^2 <= eps_m(g_i,h_i)^2.
```

By Markov, the density of `x in F_m(i)` with `delta_x(i)^2 > M_i eps_m(g_i,h_i)^2`
is at most `1/M_i` (when `eps_m(g_i,h_i) = 0`, every `delta_x(i)` on `F_m(i)` is `0`).
The complement of `F_m(i)` has density at most
`mu_m(g_i) + mu_m(h_i) + mu_m(g_i h_i)`.  Therefore

```text
G_(m,L) = { x : for all i <= L,  x in F_m(i)  and  delta_x(i)^2 <= M_i eps_m(g_i,h_i)^2 }
```

has density at least `1 - sum_(i<=L) 1/M_i - sum_(i<=L) (mu_m(g_i)+mu_m(h_i)+mu_m(g_i h_i))`.
The first sum is below `c/128`.  For each `L` choose `m_L` in the subsequence,
increasing in `L`, with the second sum below `c/128` and `mu_(m_L)(s) <= c/8`.
Then `G_(m_L, L)` has density above `1 - c/64`, so it meets `B_(m_L)`.  Pick
`x_L` in the intersection and set

```text
phi_L(g) = u_(m_L)(g, x_L)  in  U(k_(m_L)).
```

**(3) The extracted single-block sequence.**  For `i <= L`,

```text
||phi_L(g_i h_i) - phi_L(g_i) phi_L(h_i)||_F^2 = k_(m_L) delta_(x_L)(i)^2
   <= M_i k_(m_L) eps_(m_L)(g_i,h_i)^2 <= M_i C_i,
```

so `limsup_L` of the left side is at most `M_i C_i` for every pair, and the
normalized defects `delta_(x_L)(i)^2 <= M_i eps_(m_L)(g_i,h_i)^2` tend to `0`.
Also `||phi_L(s) - 1||_(2,k_(m_L))^2 >= c/4` for every `L`.

**(4) Two cases.**
- If `k_(m_L)` is bounded along a further subsequence, `||X||_op <= sqrt(k) ||X||_(2,k)`
  turns the vanishing normalized defects into vanishing operator-norm defects.
  Then `Phi(g) = [(phi_L(g))_L]` is a homomorphism from `U` into the unitary
  group of a norm matrix corona, as in step (3) of the bounded-block route,
  and `Phi(s) != 1` because `||phi_L(s) - 1||_op >= ||phi_L(s) - 1||_(2,k) >= sqrt(c)/2`.
  By `binary-leavitt-all-ranks-full-mf-radical` every homomorphism from `U`
  to an MF group is trivial, a contradiction.
- Otherwise `k_(m_L) -> infinity` along a subsequence, and `phi_L` satisfies
  (FB) and is not pointwise 2-norm trivial at `s`, contradicting (B).

Hence `||rho_m(s) - 1||_2 -> 0`, which is (A).

## (A) implies (B)

Let `phi_L : U -> U(k_L)` with `k_L -> infinity` satisfy (FB), and suppose
`||phi_L(s) - 1||_(2,k_L)` does not tend to `0` for some `s`.  View `phi_L` as
a block-monomial model with one block: `n_L = 1`, `U(k_L) wr S_1 = U(k_L)`,
trivial skeleton, label `u_L(g,1) = phi_L(g)`.  Its normalized defect is

```text
eps_L(g,h) = k_L^(-1/2) ||phi_L(gh) - phi_L(g) phi_L(h)||_F,
```

which tends to `0` because the Frobenius defect is eventually bounded and
`k_L -> infinity`.  Also `k_L eps_L(g,h)^2 = ||phi_L(gh) - phi_L(g) phi_L(h)||_F^2`,
which is bounded for all large `L` and finite for the finitely many others,
so `sup_L k_L eps_L(g,h)^2 < infinity`.  Thus the one-block model satisfies
(BB') and is not asymptotically trivial at `s`, so (A) fails.

Nothing in either direction uses a trace hypothesis or injectivity.
