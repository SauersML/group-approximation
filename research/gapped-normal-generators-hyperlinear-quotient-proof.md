---
rg: 2
id: gapped-normal-generators-hyperlinear-quotient-proof
kind: route
title: Round each gapped generator, span the conjugated active ranges, and keep the generator of largest rank
target: gapped-normal-generators-give-a-hyperlinear-quotient
requires:
  - mf-characterless-corona-image-has-hyperlinear-quotient
  - op-to-hs-shadow-residual-functoriality
  - mf-vs-tracial-radical-strict-gap
---

Choose unitary lifts `U_n(g)` of `rho(g)` for every `g in G`. For fixed
pairs, `||U_n(gh) - U_n(g)U_n(h)|| -> 0`.

**Step 1: spectral rounding.** Let `x_n = U_n(a_i)`. If `y in Q_d` is normal
with normal lifts `y_n`, then

```text
sup_(lambda in sp(y_n)) dist(lambda, sp(y)) -> 0.                     (R1)
```

Otherwise there are `eps > 0`, infinitely many `n` and eigenvalues
`lambda_n` of `y_n` with `dist(lambda_n, sp(y)) >= eps`. Pass to
`lambda_n -> lambda`; then `dist(lambda, sp(y)) >= eps`, so `y - lambda` is
invertible in `Q_d` with lifts `z_n`, `||z_n|| <= M` and
`z_n(y_n - lambda) - 1 -> 0`. A unit eigenvector `xi_n` for `lambda_n` gives
`1 - o(1) <= ||z_n (y_n - lambda) xi_n|| <= M |lambda_n - lambda| -> 0`, a
contradiction.

By `(GNG0)` and `(R1)`, for large `n` every eigenvalue of `x_n` is within
`eps_n -> 0` of `1` or at distance at least `3 delta/4` from `1`. Put
`P_(i,n) = 1_({|lambda - 1| >= delta/2})(x_n)` and

```text
A_(i,n) = (1 - P_(i,n)) + x_n P_(i,n).
```

Then `A_(i,n)` is unitary, commutes with `P_(i,n)`, is the identity on
`Ran(1 - P_(i,n))`, and `||A_(i,n) - U_n(a_i)|| <= eps_n -> 0`. Every
eigenvalue of `A_(i,n)` on `Ran P_(i,n)` satisfies `|lambda - 1| >= delta/2`.
Put `r_(i,n) = rank P_(i,n)`.

**Step 2: the invariant span.** At coordinate `n` put

```text
V_n(s) = product_j U_n(h_(s,j)) A_(i(s,j),n)^(eps_(s,j)) U_n(h_(s,j))^*.
```

Each factor preserves `U_n(h_(s,j)) Ran P_(i(s,j),n)` and is the identity on
its orthogonal complement. Let `K_n` be the span of these subspaces over all
occurrences, together with `Ran P_(i,n)` for `i = 1, ..., m`. Every factor
preserves `K_n` and is the identity on `K_n^perp`, hence so is every
`V_n(s)`, and so is every `A_(i,n)`. Moreover

```text
k_n = dim K_n <= L max_i r_(i,n),                                     (R2)
||V_n(s) - U_n(s)|| -> 0,                                             (R3)
```

by asymptotic multiplicativity of the lifts and Step 1.

**Step 3: the reblocked representation.** Fix a word `w_g` in `S` for every
`g`, and let `sigma_n(g)` be the restriction of `w_g(V_n)` to `K_n`. Since
every `w_g(V_n)` preserves `K_n` and is the identity on `K_n^perp`,
`w_g(V_n) = sigma_n(g) directSum 1` after a coordinate unitary. By `(R3)`,
`w_g(V_n) - U_n(g) -> 0` for fixed `g`. Restriction to a common invariant
subspace does not increase operator norms, so `sigma_n` is an operator-norm
asymptotic representation and `sigma directSum 1` represents `rho`. The same
comparison gives `||sigma_n(a_i) - A_(i,n)|_(K_n)|| -> 0`.

**Step 4: the surviving generator.** If `rho(a_i) = 1` for all `i`, then
`rho(G) = 1`, because `G` is the normal closure of the `a_i`. So some
`rho(a_i) != 1`, and `P_(i,n) != 0` for infinitely many `n` (when
`P_(i,n) = 0`, `||U_n(a_i) - 1|| <= eps_n`). Let `J_0` be the infinite set of
large `n` with `max_i r_(i,n) >= 1`. By pigeonhole there are an index `i*`
and an infinite `J <= J_0` on which `r_(i*,n) = max_i r_(i,n)`. For `n in J`,
by `(R2)`,

```text
||A_(i*,n)|_(K_n) - 1||_(2,tr_(k_n))^2
   = (1/k_n) sum_(active eigenvalues) |lambda - 1|^2
   >= (r_(i*,n)/k_n) delta^2/4 >= delta^2/(4L).
```

Normalized Hilbert--Schmidt norms are bounded by operator norms, so Step 3
gives `(GNG1)`.

**Part 2.** An operator-norm asymptotic representation is asymptotically
multiplicative in normalized Hilbert--Schmidt norm, so `sigma` defines a
homomorphism into the unitary group of the tracial ultraproduct along any
free ultrafilter on `J`. Its image is hyperlinear, as in
`mf-characterless-corona-image-has-hyperlinear-quotient`. By `(GNG1)`,
`a_(i*)` survives there, and it is not killed in normalized HS norm by the
operator-norm asymptotic representation `sigma`, so
`a_(i*) not in R_(infinity->2)(G)`.

**Part 3.** An element of order `k` has image with `u^k = 1`, so its
spectrum lies in the `k`th roots of unity and `(GNG0)` holds with
`delta = eta_k`. If `Rad_MF(G) = G`, then `R_(infinity->2)(G) = G`, because
`Rad_MF(G) <= R_(infinity->2)(G)` (`mf-vs-tracial-radical-strict-gap`).
Conversely, if `Rad_MF(G) != G`, some corona homomorphism is nontrivial, and
Part 2 produces a generator outside `R_(infinity->2)(G)`. A nontrivial
weak-MF group has a nontrivial corona homomorphism.

**Part 4.** If some finite normal generating set and some nontrivial `rho`
satisfied `(GNG0)` for some `delta > 0`, Part 2 would give a nontrivial
hyperlinear quotient of `R`. For finite-order generators `(GNG0)` always
holds, and `R` has a nontrivial corona homomorphism because it is nontrivial
and weak-MF.
