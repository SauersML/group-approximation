---
rg: 2
id: clock-swap-corona-compression-defect-proof
kind: route
title: A clock, its square-root permutation, and a two-fibre swap, assembled in the corona
target: mf-group-with-finite-central-compression-defect
requires: []
artifacts:
  - research/artifacts/property-t-free-counterexamples-2026-09-07.md
---

## The matrices

Let `n` run through the odd integers and put

```text
w = e^(2 pi i / n),      m = (n+1)/2,      so  2m = 1 mod n.
```

On `C^n` with indices modulo `n` define unitaries

```text
U e_j = w^j e_j,        X e_j = e_(j+1),        T e_j = e_(m j).
```

`T` is a permutation because `m` is invertible modulo `n`, and `T* e_k = e_(2k)`.
Evaluating on basis vectors,

```text
U X = w X U,      T U T* = U^2,      T X T* = X^m.       (CS1)
```

For the middle identity, `T U T* e_k = T U e_(2k) = w^(2k) e_(2mk) = w^(2k) e_k`,
which is `U^2 e_k`.  For the right one,
`T X T* e_k = T e_(2k+1) = e_(2mk+m) = e_(k+m)`.

On `C^n (+) C^n` set

```text
A = U (+) U,    B = T (+) T,    C = [[0, X],[X*, 0]].
```

These are unitary, `C^2 = 1`, and by `(CS1)`

```text
B A B* = A^2,       ||A C - C A|| = |w - 1| --> 0,       (CS2)
```

the second because `UX - XU = (w-1)XU` and `UX* - X*U = (w^(-1)-1)X*U`, both
of norm `|w-1|`.

## The group

Let `a, t, c` be the classes of `A`, `B`, `C` in the norm matrix corona
`Q = prod_n M_(2n) / directsum_n M_(2n)`, and let `G = <a,t,c>`.  Then `G` is
countable and sits in `U(Q)` by construction, so `G` is MF.  By `(CS2)`,

```text
t a t^(-1) = a^2,      c^2 = 1,      [a, c] = 1,
```

so `L = <a>` is compressed by `t` and centralized by `c`.

**`a` has infinite order.**  For fixed `k != 0`, the eigenvalues of `A^k` are
the `w^(jk)`, which run over the roots of unity of order `n/gcd(n,k)`.  That
order is at least `n/|k|` and so tends to infinity, and the roots of unity of
a large order come within `o(1)` of `-1`.  Hence
`||A^k - 1|| --> 2` and `a^k != 1`.  So `L ~= Z` and `t L t^(-1) = <a^2>` is
proper.

## The defect

Write `V = B C B*`.  By the right-hand identity of `(CS1)`,

```text
V = [[0, X^m],[X^(-m), 0]],      V^2 = 1.
```

From `U X = w X U` one gets `X^(-1) U X = w U`, hence
`X^(-m) U X^m = w^m U` and `X^m U X^(-m) = w^(-m) U`, so

```text
V A V = [[w^(-m) U, 0],[0, w^m U]],
[V, A] = V A V A^(-1) = diag(w^(-m) 1_n, w^m 1_n).        (CS3)
```

Since `n` is odd, `w^m = e^(pi i (n+1)/n) = -e^(pi i/n)`, so
`w^(+-m) --> -1` and `||[V,A] + 1|| --> 0`.  Therefore, in `Q`,

```text
k = [t c t^(-1), a] = -1,
```

a scalar, hence central; `k^2 = 1`; and `k != 1` because the constant sequence
`-1 - 1` has norm `2`.  So `<k> ~= C_2` is a nontrivial finite central subgroup
of `G` contained in `D_G(L)`, with witnesses `u = t`, `c = c`, `l = a`, and `G`
is MF.

## What this witness adds

The centralizing element is itself an involution, and the defect is displaced
from the identity by exactly `2` — in operator norm, and also in normalized
Hilbert--Schmidt norm, since `k` is the scalar `-1` in every coordinate.  So
the surviving defect is not a vanishing-rank phenomenon, and the active-core
reblocking of `torsion-normal-generator-has-full-support-corona-core`, which
converts a corona-visible finite-order mark into a Hilbert--Schmidt-visible
one, has nothing left to repair here: the mark is already maximally visible on
both sides.  Read against the transport corollary `cor:defect-hs`, which makes
every element of `D_G(L)` Hilbert--Schmidt-null when `L` has property (T),
this is the sharpest possible failure of that corollary without the
hypothesis.

Not claimed: that `G` is finitely presented, residually finite, or given by a
presentation.  It is a subgroup of a corona, specified by generators.  The
solvable witness supplies a concrete group instead.
