---
rg: 2
id: kt-sofic-monomial-commutant-core-is-normalized-proof
kind: route
title: Monomial rigidity, Kun--Thom 4.1 on the doubled model, and invariance of the generated algebra
target: kt-sofic-monomial-commutant-core-is-normalized
requires: [kun-thom-sofic-centralizer-normalization]
---

Notation as in the target. All 2-norms are normalized. For permutation matrices
`p, q` in `M_n`, the normalized Hamming distance is `d_H(p,q) = ||p - q||_2^2 / 2`,
so commutation in `S_U` and in `M` agree for permutations.

**Step 1 (monomial rigidity).** Let `m = d p` with `d in U(D)` and `p in S_U`, and
suppose `m sigma(gamma) m^* = sigma(gamma)` for some `gamma in Gamma`. Put
`pi = p sigma(gamma) p^-1` and `d' = (pi^-1 d pi) d^*`, a diagonal unitary. Then
`m sigma(gamma) m^* = pi d'`. At level `n`, `pi_n d'_n` and `sigma_n(gamma)` are monomial
matrices supported on the graphs of `pi_n` and `sigma_n(gamma)`. At a point where the two
permutations differ, the difference has two disjoint unit entries in its column;
where they agree it has one entry `d'_n(y) - 1`. Hence

```text
||pi_n d'_n - sigma_n(gamma)||_2^2  >=  2 d_H(pi_n, sigma_n(gamma)),
```

so `p` commutes with `sigma(gamma)` in `S_U`, and then `d' = 1` in `M`, i.e.
`sigma(gamma)^-1 d sigma(gamma) = d`. Conversely such `p` and `d` give a commuting `m`.
This is item 1.

**Step 2a (centralizer).** `kun-thom-sofic-centralizer-normalization` gives
`sigma(g) C_(S_U)(sigma(Gamma)) sigma(g)^-1 = C_(S_U)(sigma(Gamma))` for every `g in G`.

**Step 2b (invariant diagonal, by doubling).** Let `e = (e_n)` be a projection in
`D cap R`, with each `e_n` a diagonal projection. On `Y_n` disjoint union `Y_n`, let

```text
sigma2_n = sigma_n (+) sigma_n,     s_(e,n) = [[1 - e_n, e_n], [e_n, 1 - e_n]].
```

`sigma2` is an injective sofic representation with canonical trace, since
`sigma2_n(g)` has the same fixed-point fraction as `sigma_n(g)`, and each `s_(e,n)` is a
permutation matrix. For `u = sigma_n(gamma)`, the off-diagonal block of
`s_(e,n) sigma2_n(gamma) s_(e,n) - sigma2_n(gamma)` is `(1-e)ue + eu(1-e)`, and the diagonal block is
`(1-e)u(1-e) + eue - u`. Both are bounded in 2-norm by a constant times
`||[e_n, u]||_2`. Conversely, compressing the off-diagonal block by `e` on either
side recovers `(1-e)ue` and `eu(1-e)`, whose sum controls `[e,u]`. So `s_e` commutes with
`sigma2(Gamma)` exactly when `e in R`. Exactly at every level,

```text
sigma2_n(t) s_(e,n) sigma2_n(t)^-1 = s_(e',n),    e'_n = sigma_n(t) e_n sigma_n(t)^-1.
```

Applying `kun-thom-sofic-centralizer-normalization` to `sigma2` shows that `s_(e')`
commutes with `sigma2(Gamma)`, so `sigma(t) e sigma(t)^-1 in D cap R` for every `t in G`.
Permutations normalize `D`, and `D cap R` is spanned in norm by its projections. So
`sigma(g)(D cap R)sigma(g)^-1 <= D cap R`, with equality after applying it to `g^-1`.

**Step 2c (generated algebra).** `Ad sigma(g)` is a normal `*`-automorphism of `M`
that leaves the generating set `C_(S_U)(sigma(Gamma)) union (D cap R)` invariant, so it
leaves its double commutant `N_sigma` invariant. This is item 2.

**Step 3 (projection off the core).** `Ad sigma(g)` preserves the trace and `N_sigma`, so
it commutes with the trace-preserving conditional expectation `E_(N_sigma)`. If
`z in R`, then `E_(N_sigma)(z) in N_sigma <= R` and its transport stays in `N_sigma <= R`.
Hence `sigma(g)(z - E_(N_sigma)(z))sigma(g)^* notin R` whenever `sigma(g) z sigma(g)^* notin R`.
This is item 3.

**Step 4 (relative bicommutant).** Let `S = C_(S_U)(sigma(Gamma)) union (D cap R)`. By Steps
2a and 2b, `sigma(g) S sigma(g)^-1 = S`, so `Ad sigma(g)` preserves `B_sigma = S' cap M` and
`A_sigma = B_sigma' cap M`. Every `sigma(gamma)` commutes with `S`, so `sigma(Gamma) <= B_sigma`,
and hence `A_sigma <= sigma(Gamma)' cap M = R`. Also `S <= A_sigma`, so `N_sigma <= A_sigma`.

For the conditional add-on, assume `C_(S_U)(sigma(Gamma)) = prod_U A_n` with genuine finite
groups `A_n` (Alekseev--Thom Theorem 3.1 provides this after padding by `o(|Y_n|)` points,
which does not change `M`; nothing below uses that import). If `x in M` commutes with every sequence in
`prod_U A_n`, then `sup_(a in A_n) ||[x_n, a]||_2 -> 0` along `U`: otherwise a sequence of bad
`a_n` would be an element of `prod_U A_n` not commuting with `x`. Averaging `a x_n a^-1`
over the finite group `A_n` is the conditional expectation onto `A_n' cap M_n`, so
`x in prod_U (A_n' cap M_n)`. The reverse inclusion is clear. The same argument, averaging
over the compact unitary group of `A_n' cap M_n`, gives
`(prod_U (A_n' cap M_n))' cap M = prod_U C[A_n]`. These are the displayed identifications.
