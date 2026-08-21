---
rg: 2
id: block-trace-reduction-of-the-tower-leak-floor-proof
kind: route
title: Center-valued trace splitting, Cauchy-Schwarz spread radii, and the matched center identity
target: block-trace-reduction-of-the-tower-leak-floor
requires: []
---

**Step 1 (orbit splitting).**  `W K W*` has `B`-blocks
`u_sigma K_sigma u_sigma*` with independent `u_sigma in
U(mtilde_sigma)`.  Pair against `K-tilde = V_0* K V_0`:

```text
ell(K, W) = <W K W*, K-tilde>
          = sum_sigma w_sigma tr(u_sigma K_sigma u_sigma* Y_sigma*)
            / mtilde_sigma,
```

where `Y_sigma` is the block compression of `K-tilde` (not scalar,
since `K-tilde` need not lie in `B`).  Split
`K_sigma = p_sigma 1 + K_sigma^0` and `Y_sigma = y_sigma 1 +
Y_sigma^0` into scalar and traceless parts.  The cross terms vanish
under the block trace, and

```text
tr(u K u* Y*)/m = p conj(y) + tr(u K^0 u* (Y^0)*)/m,
```

with `|tr(u K^0 u* (Y^0)*)/m| <= ||K^0||_2 ||Y^0||_2` (normalized
Cauchy--Schwarz) — this is the exact radius bound for the
C-numerical-range of `Y` relative to `K` (a compact star-shaped set
with star center at the product of the barycenters, by
Cheung--Tsing).  For unitary `K_sigma`,
`||K_sigma^0||_2^2 = 1 - |p_sigma|^2` exactly.  Summing gives
`(BTR1)`.

**Step 2 (matched centers).**  `y_sigma` is the pairing of `K-tilde`
with the normalized central projection `P_sigma^B / mtilde_sigma
d_sigma`.  The dictionary conjugates `rho(Q_0)''` onto `rho(Q_1)''`,
hence carries the isotypic center of `A` onto that of `B`:
`V_0 P_tau^A V_0* = P_(match(tau))^B`.  Therefore

```text
y_sigma = <P_sigma^B, V_0* K V_0> / (mtilde d)
        = <V_0 P_sigma^B V_0*, K> / (mtilde d)
        = <P_(match^(-1)(sigma))^A, K> / (mtilde d),
```

which is a fixed weighted combination of the block traces of `K` in
`A`, themselves fixed weighted combinations of the `Z`-block traces
by branching.  Substituting into the locked sum yields a Hermitian
quadratic form `p* M p` whose matrix is assembled from the two
branching tables and the matching — `(BTR2)` — and `(BTR3)` follows
by the triangle inequality, minimizing over the admissible trace
vectors.

**Step 3 (constraints on `p`).**  Unitarity of each `K_sigma` gives
`|p_sigma| <= 1` with equality forced when `mtilde_sigma = 1`;
`tau(K) = sum` (weights) `p`-data gives the linear constraint; and
`K in Z` makes the whole vector `p` the image of the smaller vector
of `Z`-block traces under the branching matrix, which both links the
coordinates and transfers the multiplicity-one rigidity of `Z`-blocks
(a `Z`-block of multiplicity one contributes a PHASE to every
`B`-block it feeds).  All constants in `(BTR1)`-`(BTR3)` are
explicit, dimension-free in the multiplicity direction, and computed
for the prototype in the recorded tables.
