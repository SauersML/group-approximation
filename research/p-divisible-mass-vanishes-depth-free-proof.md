---
rg: 2
id: p-divisible-mass-vanishes-depth-free-proof
kind: route
title: The twist moves every diagonal depth type off the diagonal, and Clifford balancing puts most of each level on the diagonal
target: p-divisible-lambda-exact-mass-vanishes-at-large-primes
requires: []
---

**Step 1 (depth types).**  For an irreducible constituent `sigma` of
`rho'|_(C_0)` put `beta(sigma) = min{b >= 0 : sigma trivial on e_12(p^b m') and e_23(p^b m')}`
and `gamma(sigma) = min{g >= 1 : sigma trivial on e_21(p^g m') and e_32(p^g m')}`;
all these elements lie in `C_0 = {c in SL_3(Z) : p | c_21, p^2 | c_31, p | c_32}`,
and both minima exist because `rho'` is trivial on `Gamma(p^D m')`.  Write
`nu(b, g)` for the total weight of constituents of type `(b, g)` in the
isotypic weight measure `w_1` of `rho'|_(C_0)`.

**Step 2 (the twist on types).**  With `h = diag(p,1,1/p)` and `J` the
signed permutation matrix of `(1 3)`, `g = J h` normalizes `C_0` and

```text
Ad(g) e_12(x) = e_32(+-p x),   Ad(g) e_23(x) = e_21(+-p x),
Ad(g) e_21(x) = e_23(+-x/p),   Ad(g) e_32(x) = e_12(+-x/p).
```

For `sigma^iota = sigma o Ad(g)^-1`: `sigma^iota` is trivial on
`e_32(p^g m')` and `e_21(p^g m')` iff `sigma` is trivial on `e_12(p^(g-1) m')`
and `e_23(p^(g-1) m')`, so `gamma(sigma^iota) = beta(sigma) + 1`; and
`sigma^iota` is trivial on `e_12(p^b m')` and `e_23(p^b m')` iff `sigma` is
trivial on `e_32(p^(b+1) m')` and `e_21(p^(b+1) m')`, so
`beta(sigma^iota) = max(gamma(sigma) - 1, 0)`.  Hence the twist maps type
`(a, a)` to type `(a - 1, a + 1)` for every `a >= 1`, and the weight measure
`w_2 = iota_* w_1` of the twist satisfies `w_2(off-diagonal types) >= w_1(diagonal types)`.

**Step 3 (Clifford balancing on each level).**  Decompose `rho'` into
irreducible constituents `pi' = pi'_p (x) pi'_(m')` of `SL_3(Z/p^D) x SL_3(Z/m')`
and let `nu_a` be the weight of those whose `p`-part has level exactly `a`.
For `a >= 1`, Step 4 of `lambda-exact-p-divisible-ultra-deep-proof` shows
that the normalized dimension of the subspace of `pi'` fixed by
`e_12(p^(a-1) m')` is at most `1 - c_p`; a `C_0`-constituent of `pi'` with
`beta <= a - 1` lies in that subspace, so constituents with `beta = a` carry
weight at least `c_p nu_a` and those with `beta <= a - 1` at most
`(1 - c_p) nu_a`.  The same orbit count for the hyperplane `Y_12 = 0`,
which is carried to `Y_21 = 0` by a Weyl element of `SL_3(F_p)`, gives the
identical bounds for `e_21(p^(a-1) m')` when `a >= 2` (then this element is
in `C_0`): constituents with `gamma = a` carry at least `c_p nu_a`, those
with `gamma <= a - 1` at most `(1 - c_p) nu_a`.  For `a = 1` every
constituent has `gamma = 1`.  Consequently, on the level-`a` part
(`a >= 1`):

```text
weight of diagonal type (a, a)      >=  (2 c_p - 1) nu_a,
weight of off-diagonal types        <=  2 (1 - c_p) nu_a.
```

Level `0` (trivial `p`-part) extends to a representation of `SL_3(Z[1/p])`
through `SL_3(Z/m')`, on which `Ad(g)` is inner, so its weight measure is
`iota`-invariant and contributes nothing to the total variation.

**Step 4 (comparison).**  Let `O` be the set of off-diagonal types.  By
Steps 2--3, `w_2(O) >= w_1(diag) >= (2 c_p - 1)(1 - nu_0)` up to the
`iota`-invariant level-`0` mass, and `w_1(O) <= 2(1 - c_p)(1 - nu_0)` plus the
same level-`0` mass.  Hence
`TV(w_1, w_2) >= w_2(O) - w_1(O) >= (4 c_p - 3)(1 - nu_0)`.

**Step 5 (the upper bound).**  Steps 1--2 of
`lambda-exact-p-divisible-ultra-deep-proof` at `k = 1` give a contraction
`T' = rho'(J) T` intertwining `rho'|_(C_0)` with `rho' o Ad(g)|_(C_0)`, with
`||rho'(J) H - T'||_2 <= 3 epsilon/kappa_0`, so `TV(w_1, w_2) <= 12 epsilon/kappa_0`.
Combining with Step 4 gives `(PV1)`.  No depth, cell structure or regular
trace enters.
