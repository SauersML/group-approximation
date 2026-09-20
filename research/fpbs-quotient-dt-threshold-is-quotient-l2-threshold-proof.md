---
rg: 2
id: fpbs-quotient-dt-threshold-is-quotient-l2-threshold-proof
kind: route
title: Push the length-truncated DT iteration to the quotient, and make pushed ball boundary measures small below p^Q by thinning against a slightly larger parameter
target: fpbs-quotient-dt-threshold-is-quotient-l2-threshold
requires:
  - fpbs-quotient-l2-threshold-sandwich
  - fpbs-lq-threshold-power-monotonicity
  - fpbs-spectral-dt-threshold-equals-l2-threshold
---

Notation as in the target. For nonnegative functions on a group, `*` is
convolution, `||f||_Q` is the (possibly infinite) convolution norm on
`l2(Q)` of the sandwich node, and `a_D = sum_{d in D} delta_d`. Convolution
norms of nonnegative kernels are monotone under entrywise domination and
submultiplicative, and `||pi_* a_D||_Q <= |D|`. Because `N` is normal,
`pi_*(f * g) = pi_* f * pi_* g` for nonnegative `f, g` on `Gamma`.

**Step 1 (length-truncated DT inequality).** Let `tau^(m)(x)` be the
probability that `o` and `x` are joined by an open path of length at most
`m`, so `tau^(0) = delta_o` and `tau^(m)` increases to `tau_p(o, .)`. For
`x` not in `S` and `m >= 1`,

```text
tau^(m)(x) <= sum_v nu_{S,p}(v) tau^(m-1)(v^{-1} x).
```

*Proof.* Fix an open path `gamma` from `o` to `x` of length at most `m`, and
let `C` be the cluster of `o` in the subgraph induced by `S`. Let `u` be the
last vertex of `gamma` in `C` and `v` the next one. The edge `uv` is open, so
`v` is not in `S` (otherwise `v` would be in `C`). The rest of `gamma` runs
from `v` to `x` off `C`, with length at most `m - 1`. Condition on `C = A`.
This event depends only on edges with an endpoint in `A` inside `S` and the
closed boundary of `A` in `S`. The event "`v` joined to `x` by an open path of
length at most `m - 1` avoiding `A`" depends only on edges with no endpoint
in `A`, so the two are independent, and the second has probability at most
`tau^(m-1)(v^{-1} x)`. Summing over `A`, `u`, `v` gives the bound, with
`P_p(o <->_S u) p` summed over the edges `uv` in `Delta S` ending at `v`,
which is `nu_{S,p}(v)`. ∎

For `x` in `S`, `tau^(m)(x) <= 1 = 1_S(x)`. So
`tau^(m) <= 1_S + nu * tau^(m-1)`, and by induction on `m`,

```text
tau^(m) <= sum_{k=0}^{m} nu^{*k} * 1_S.
```

**Step 2 (item 1).** Push forward and let `m -> infinity` (monotone
convergence):
`sigma^N_p <= sum_k (pi_* nu)^{*k} * pi_* 1_S` entrywise. If
`sp_Q(pi_* nu) < 1`, then `sum_k ||rho_Q(pi_* nu)^k|| < infinity` by the
spectral radius formula, and `||pi_* 1_S||_Q <= |S|`. ∎

**Step 3 (item 2).** Let `p < p' < p^Q` and `s = log p / log p' > 1`, so
`p = p'^s`. By thinning (item 1 of `fpbs-lq-threshold-power-monotonicity`,
with exponent `1/s`), `tau_p <= tau_{p'}^s`.

* `M' = ||sigma^N_{p'}||_Q < infinity`. Testing against `delta`'s gives
  `sigma^N_{p'}(q) <= M'` for each `q` and `||sigma^N_{p'}||_{l2(Q)} <= M'`.
  So for each `eps > 0` only finitely many cosets have
  `sigma^N_{p'}(q) >= eps`, and inside each only finitely many `x` have
  `tau_{p'}(o,x) >= eps`. Hence `eps_R = sup_{|x| = R} tau_{p'}(o,x) -> 0`.
* Step 1 of the proof of `fpbs-spectral-dt-threshold-equals-l2-threshold`
  gives `nu_{B_R,p} <= p (tau_p 1_{S_R}) * a_D` entrywise, where
  `S_R = {|x| = R}`.
* On `S_R`, `tau_p <= tau_{p'}^s <= eps_R^{s-1} tau_{p'}`. Pushing forward,
  `pi_*(tau_p 1_{S_R}) <= eps_R^{s-1} sigma^N_{p'}`.

Therefore

```text
||rho_Q(pi_* nu_{B_R,p})|| <= p |D| eps_R^{s-1} ||sigma^N_{p'}||_Q -> 0.   ∎
```

**Step 4 (item 3).** Item 1 gives `p^Q_sDT <= p^Q`. Item 2 gives a ball
certificate at every `p < p^Q`, so `p^Q_sDT >= p^Q`. ∎

**Step 5 (items 4 and 5).** Part 6 of `fpbs-quotient-l2-threshold-sandwich`
gives `||sigma^N_{p_c}||_Q < infinity` iff `p_c < p^Q`. If `p_c < p^Q`, item 2
at `p = p_c` gives a ball with norm below one. A norm below one gives a
spectral radius below one, and item 1 then gives
`||sigma^N_{p_c}||_Q < infinity`. Item 5 is item 4 combined with C1 of
`fpbs-relative-threshold-is-quotient-l2-threshold`: under `E'(G,N)` the gap
`p_c < p_c(N;G)` is alternative (i). ∎

**Remark (why not the sphere bootstrap).** The tail bootstrap of
`fpbs-sphere-fibre-operator-iff-critical-fibre-l2` controls `sigma^N_p`
off large `Q`-balls. A `Gamma`-sphere `S_R` projects into the `Q`-ball of
radius `R`, not off it, and meets every coset near `N`. So the `N = {1}`
proof does not generalise, and thinning replaces it. The price is that
item 2 has no explicit rate at `p = p_c` unless one is given a
`p' > p_c` with a bound on `||sigma^N_{p'}||_Q`.
