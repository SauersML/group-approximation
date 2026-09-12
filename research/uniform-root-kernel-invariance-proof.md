---
rg: 2
id: uniform-root-kernel-invariance-proof
kind: route
title: Cross the root-of-unity gap to identify the two kernels, then invert a left multiplication on a finite quotient
target: uniform-root-kernel-invariance-kills-one-sided-defect
requires: []
artifacts:
  - research/artifacts/root-kernel-uniformity-gap-2026-09-08.md
---

## 1. The spectral gap

Let `u in U(d)` satisfy `u^m = 1` and `u != 1`.  With `omega = e^(2 pi i/m)`
the operators

```text
P_k = (1/m) sum_(j=0)^(m-1) omega^(-kj) u^j
```

are mutually orthogonal projections summing to `1`, with `u P_k = omega^k P_k`;
both identities are finite geometric sums.  If `u != 1` then `P_k != 0` for
some `k != 0`, and on the range of that projection `u - 1` acts as the scalar
`omega^k - 1`, so

```text
|| u - 1 || >= |omega^k - 1| = 2 |sin(pi k/m)| >= 2 sin(pi/m) = kappa_m.  (G)
```

Since `mR = 0` and `X` is additive, `X(a)^m = X(ma) = X(0) = 1`, and likewise
for `Y`; so `(G)` applies to every value of either root map.

## 2. The two kernels coincide

Suppose `X(a) = 1`.  Then `(RK2)` reads `|| 1 - Y(a) || < kappa_m`, so `(G)`
forces `Y(a) = 1`.  Conversely if `Y(a) = 1` then
`|| C X(a) C* - 1 || < kappa_m`, and conjugation preserves the operator norm,
so `|| X(a) - 1 || < kappa_m` and `X(a) = 1`.  Hence

```text
I := ker X = ker Y,
```

an additive subgroup of `R` because `X` is an additive homomorphism.

## 3. `R/I` is finite

The image of `X` is a set of commuting unitaries -- `X` is a homomorphism from
an abelian group -- each of order dividing `m`.  Split `C^d` along the
eigenspaces of one non-scalar member of the family and recurse inside each
summand; commutativity preserves every summand and each proper split raises
the number of nonzero orthogonal summands, so after at most `d - 1` splits the
family is simultaneously diagonal.  In that basis every member is diagonal with
entries among the `m` `m`-th roots of unity, so the image has at most `m^d`
elements.  `X` induces an injection of `R/I` into that image, so `R/I` is
finite.

## 4. The kernel is invariant under the two left multiplications

Let `a in I` and `b in {s,t}`.  Then `X(a) = 1`, so `[U_b, X(a)] = 1`, and
`(RK3)` reads `|| 1 - Y(ba) || < kappa_m`.  By `(G)`, `Y(ba) = 1`, i.e.
`ba in I`.

So left multiplication by `s` and by `t` descends to additive endomorphisms
`S, T` of `R/I`.  Nothing here needs `I` to absorb multiplication on the right,
and nothing needs `I` to be an ideal.

## 5. Inverting on a finite group

For `a in R`, `t(sa) = (ts)a = a`, so `T S = id` on `R/I`.  Hence `S` is
injective; `R/I` is finite by step 3, so `S` is bijective, and a left inverse of
a bijection is its two-sided inverse.  Therefore `S T = id`, i.e.

```text
s(ta) - a = (st - 1)a = -qa  in  I     for every a in R,
```

so `qa in I` and `X(qa) = Y(qa) = 1`, which is `(RK4)`.

## 6. The exact-representation corollary

For a finite-dimensional unitary `rho` of `E_n(R)`, `n >= 3`, the substitutions
listed on the target satisfy `(RK2)` and `(RK3)` with error `0`, because
`w e_23(a) w^-1 = e_13(a)` and `[e_12(b), e_23(a)] = e_13(ba)` are identities of
elementary matrices, `w = e_12(1) e_21(-1) e_12(1)` having upper-left block
`[[0,1],[-1,0]]`.  Additivity of `a -> e_ij(a)` makes `X` and `Y` genuine
additive homomorphisms.  So `(RK4)` gives `rho(e_13(qa)) = 1`.

Signed permutation matrices of the elementary group are products of the same
two-coordinate words `w` and move any ordered pair of distinct coordinates to
any other, changing the coefficient at most by a sign, which does not change a
kernel.  So `rho(e_ij(qa)) = 1` for all `i != j`.
