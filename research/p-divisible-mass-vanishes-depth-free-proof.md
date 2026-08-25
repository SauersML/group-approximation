---
rg: 2
id: p-divisible-mass-vanishes-depth-free-proof
kind: route
title: The twist moves every diagonal depth type off the diagonal, with a separate transvection bound at level one
target: p-divisible-lambda-exact-mass-vanishes-at-large-primes
requires:
  - lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible
  - orthogonal-kazhdan-powers-have-quadratic-depth-loss
---

**Step 1 (depth types).**  For an irreducible constituent `sigma` of
`rho'|_(C_0)` put

```text
beta(sigma)  = min{b >= 0 : sigma is trivial on
                   e_12(p^b m') and e_23(p^b m')},
gamma(sigma) = min{g >= 1 : sigma is trivial on
                   e_21(p^g m') and e_32(p^g m')}.
```

All four families lie in
`C_0 = {c in SL_3(Z) : p | c_21, p^2 | c_31, p | c_32}` at the indicated
depths, and the minima exist because `rho'` is trivial on
`Gamma(p^D m')`.  Decompose `rho'` first by exact `p`-level and then into
`C_0`-irreducibles; all weight statements below use this occurrence/dimension
measure before equal `C_0`-types from different levels are aggregated.

**Step 2 (the twist on types).**  With `J` the involutive signed permutation
matrix reversing coordinates, `g=Jh` normalizes `C_0` and

```text
Ad(g) e_12(x) = e_32(+-p x),   Ad(g) e_23(x) = e_21(+-p x),
Ad(g) e_21(x) = e_23(+-x/p),   Ad(g) e_32(x) = e_12(+-x/p).
```

For `sigma^iota = sigma o Ad(g)^-1` this gives

```text
(beta(sigma^iota), gamma(sigma^iota))
  = (gamma(sigma)-1, beta(sigma)+1).                                    (DP1)
```

In particular `(a,a)` maps to `(a-1,a+1)` for every `a>=1`.

**Step 3 (Clifford balancing from level two onward).**  Decompose `rho'`
into irreducible constituents
`pi' = pi'_p (x) pi'_(m')` of
`SL_3(Z/p^D) x SL_3(Z/m')`, and let `nu_a` be the weight of those whose
`p` part has exact level `a`.

For `a>=2`, the last layer
`Gamma(p^(a-1))/Gamma(p^a) = sl_3(F_p)` is abelian.  Step 4 of
`lambda-exact-p-divisible-ultra-deep-proof` shows that the normalized
dimension fixed by `e_12(p^(a-1)m')` is at most `1-c_p`.  A restricted
constituent with `beta<=a-1` lies in that fixed subspace, so `beta=a` has
weight at least `c_p nu_a`.  Weyl symmetry gives the same conclusion for
`gamma=a`.  Since all restricted constituents have `beta,gamma<=a`, the
union bound gives

```text
weight of type (a,a)              >= (2 c_p-1) nu_a,
weight of all off-diagonal types  <= 2(1-c_p) nu_a.                     (DP2)
```

This step deliberately excludes `a=1`: there
`Gamma(1)/Gamma(p)=SL_3(F_p)`, not the additive Lie layer.

**Step 4 (the level-one transvection bound).**  In `SL_3(F_p)` let
`U_12,U_23,U_31` be the three parameter root subgroups.  They are conjugate
and generate the group: their commutators give `U_13,U_32,U_21`, and the six
root subgroups generate `SL_3(F_p)`.  If `pi'_p` is a nontrivial irreducible,
then

```text
Fix(U_12) cap Fix(U_23) cap Fix(U_31) = 0.
```

The three fixed-space codimensions are equal, and subadditivity of
codimension therefore gives

```text
dim(pi'_p) <= sum_(ij in {12,23,31}) codim Fix(U_ij),
```

so each root subgroup has nonfixed normalized dimension at least `1/3`.
Every level-one `C_0`-constituent has `gamma=1`; those with `beta=0` lie in
`Fix(U_12)`.  Hence type `(1,1)` carries weight at least `nu_1/3`.

The level-zero part has type `(0,1)` and factors through
`SL_3(Z/m')`.  Because `p` is invertible modulo `m'`, `Ad(g)` is inner on
that quotient, so its isotypic weight measure is twist-invariant.

**Step 5 (one type set compares all positive levels).**  Let

```text
S = {(a-1,a+1) : a >= 1}.
```

By `(DP1)--(DP2)` and Step 4,

```text
w_2(S) >= (2 c_p-1) sum_(a>=2) nu_a + (1/3) nu_1.                       (DP3)
```

Level zero and level one give no mass to `w_1(S)`.  Every type in `S`
contributed by a level `a>=2` summand is off diagonal, so `(DP2)` gives

```text
w_1(S) <= 2(1-c_p) sum_(a>=2) nu_a.                                    (DP4)
```

Consequently

```text
TV(w_1,w_2) >= w_2(S)-w_1(S)
             >= (4 c_p-3) sum_(a>=2) nu_a + (1/3) nu_1
             >= min(4 c_p-3,1/3) (1-nu_0).                             (DP5)
```

This remains valid after equal `C_0`-irreducibles from distinct ambient
levels are aggregated, because both isotypic weight and its pushforward are
linear in the occurrence/dimension measures.

**Step 6 (the upper bound).**  Steps 1--2 of
`lambda-exact-p-divisible-ultra-deep-proof` at `k=1` give a contraction
`T' = rho'(J)T` intertwining `rho'|_(C_0)` with its `Ad(g)`-twist.  The safe
linear estimate is

```text
TV(w_1,w_2) <= 12 epsilon/kappa_0.
```

With `epsilon` normalized exactly as in `(UD1)`, `T` is the orthogonal
Hilbert--Schmidt projection of `H` onto the intertwiner space, and
`orthogonal-kazhdan-powers-have-quadratic-depth-loss` gives

```text
TV(w_1,w_2) <= epsilon^2/kappa_0^2.
```

Combining either upper bound with `(DP5)` proves `(PV1)` and
`(PV1-square)`.  No depth, cell structure, or regular-trace hypothesis
enters.
