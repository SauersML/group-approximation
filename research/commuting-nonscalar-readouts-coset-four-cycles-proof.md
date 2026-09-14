---
rg: 2
id: commuting-nonscalar-readouts-coset-four-cycles-proof
kind: route
title: Support separation in the twisted group algebra forces a four-cycle for commuting nonscalar readouts
target: commuting-nonscalar-readouts-force-coset-four-cycles
requires: []
---

Notation as in `commuting-nonscalar-readouts-force-coset-four-cycles`.

## Twisted basis

Because `J` is central, `p_omega` is a central idempotent and `J^k p_omega =
omega(J^k) p_omega`. Fix a section `s : A/J -> A`. Then
`{ s(t) p_omega : t in A/J }` is a basis of `C[A] p_omega`, and for `t, u in
A/J` we have `s(t) s(u) p_omega = kappa(t,u) s(tu) p_omega` with
`kappa(t,u)` a value of `omega`, hence nonzero. For a subgroup `H >= J`,
`C[H] p_omega` is the span of `s(t) p_omega` with `t in H/J`.

Every element `z in C[A] p_omega` is a `J`-equivariant function on `A`
(`z(gj) = conj(omega(j)) z(g)` up to the fixed normalization), and it lies in
`C[H] p_omega` exactly when it vanishes off `H`.

## Proof of (CN2)

An element of `C[H] p_omega` vanishes off `H`, and an element of `C[K]
p_omega` vanishes off `K`. So an element of both vanishes off `H cap K`, and
lies in `C[H cap K] p_omega`. If `H cap K = J`, this is `C p_omega`, so a
nonscalar readout in both algebras forces `H cap K` strictly larger than `J`.
A context that forces `y_(v') in C*(1, y_v)` puts `y_(v')` in
`C[H_v] p_omega` and, by definition of local data, in `C[H_(v')] p_omega`.

## Proof of (CN1)

Write `x = lambda p_omega + a` and `y = mu p_omega + b`, where `a` is
supported on the cosets `t in H/J` with `t != J`, and `b` on the cosets
`u in K/J` with `u != J`. The terms `lambda p_omega`, `mu p_omega` are central,
so `[x, y] = [a, b] = ab - ba`.

1. **Supports.** `ab` is supported on the cosets `tu` and `ba` on the cosets
   `ut`, with `t in H/J`, `u in K/J`, `t, u != J`.
2. **Separation.** Suppose, for contradiction, `HK cap KH = H union K`. Take
   `h in H \ J`, `k in K \ J`. If `hk in H` then `k in H cap K = J`, and if
   `hk in K` then `h in J`; so `hk` is outside `H union K` and hence outside
   `KH`. Every coset `ut` lies inside `KH`, so the supports of `ab` and `ba` are
   disjoint, and `ab - ba = 0` forces `ab = 0`.
3. **Injectivity.** The map `(t, u) -> tu` from `(H/J \ {J}) x (K/J \ {J})` to
   `A/J` is injective: if `hkJ = h'k'J`, then `h'^(-1) h = k' j k^(-1)` for
   some `j in J`, and this element lies in `H cap K = J`, so `hJ = h'J`, and
   then `kJ = k'J`. Hence the coefficient of `ab` at the coset `tu` is
   `kappa(t,u) a_t b_u`, and `ab = 0` gives `a_t b_u = 0` for all `t, u`. So
   `a = 0` or `b = 0`, i.e. `x` or `y` lies in `C p_omega`. This contradicts
   the hypothesis, so `HK cap KH` is strictly larger than `H union K`.
4. **Four-cycle.** Pick `z in (HK cap KH) \ (H union K)`, `z = hk = k'h'` with
   `h, h' in H` and `k, k' in K`. Then `h, h', k, k'` are all outside `J`: for
   instance `h in J` would give `z = hk in K`. Consider the vertices `H`, `hK`,
   `zH = k'H` and `K` of `Gamma(A; H, K)`, joined by the edges `hJ` (from `H`
   to `hK`), `zJ` (from `hK` to `zH`), `k'J` (from `zH` to `K`) and `J` (from
   `K` to `H`). Each edge coset is contained in both endpoints.
   - `H != zH` because `z not in H`, and `hK != K` because `h not in K`.
   - The four edge cosets are distinct:
     - `hJ != J`, `zJ != J` and `k'J != J`, since `h, z, k'` are outside `J`;
     - `zJ != hJ`, since `k` is outside `J`;
     - `zJ != k'J`, since `h'` is outside `J`;
     - `hJ != k'J`, because `hJ` lies in `H`, `k'J` lies in `K`, and a common
       coset would lie in `H cap K = J`.
   So this is a four-cycle, and the girth is 4, which gives `m(H, K) = 2`.

## Proof of (CN3)

Readouts of variables in one context commute by definition of local data.
If `H_v cap H_w = J` and both readouts are nonscalar, (CN1) gives `m = 2`. If
`H_v cap H_w` is larger than `J`, the coset multigraph has parallel edges and
`m = 1`.
