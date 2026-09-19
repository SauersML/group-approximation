---
rg: 2
id: lifted-thompson-t-mf-radical-dichotomy-proof
kind: route
title: "Simplicity of T and perfectness of T-bar confine the radical to all or the centre; the dilation g(2x)/2 empties the centre; rotation centralizers carry the rest down to T and V"
target: lifted-thompson-t-mf-radical-dichotomy
requires:
  - universal-mf-quotient
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - lifted-thompson-t-quotients-are-rotation-centralizers
---

Notation as in the target.  No step uses Property `(T)`, a Kazhdan subgroup,
a spectral gap or a trace.

**Imports.**
- (I1) `T` and `V` are infinite simple groups, `T` is finitely presented, and
  `T <= V` (Cannon--Floyd--Parry, *Introductory notes on Richard Thompson's
  groups*, Enseign. Math. 42 (1996); standard, and the same import (I1) as in
  `lifted-thompson-t-perfect-centre-cubically-elliptic-proof`; theorem numbers
  not re-checked).
- (I2) An extension of a finitely presented group by a finitely presented
  group is finitely presented (P. Hall; standard).
- (P1) `T̄` is perfect: item 2 of `lifted-thompson-t-perfect-centre-cubically-elliptic`.
- (P2) For every `k >= 0`, `iota_k(g) = p(lambda^k(g))`, where
  `lambda^k(g)(x) = 2^(-k) g(2^k x)`, is a homomorphism from `T̄` **onto**
  `C_T(r_k)`, with kernel `<z^(2^k)>`: the statement of
  `lifted-thompson-t-quotients-are-rotation-centralizers`.
- (U) `universal-mf-quotient`: for a countable group `G`, `Rad(G)` is the kernel
  of one homomorphism to the unitary group of a norm matrix corona, and `G` is
  MF iff `Rad(G) = 1`.

## Step 0. Three formal properties of `Rad`

- (R1) *Push-forward.*  If `f : G -> K` is a homomorphism, then
  `f(Rad(G)) <= Rad(K)`.  Indeed, for every corona representation `pi` of `K`,
  `pi o f` is a corona representation of `G`, so it kills `Rad(G)`.
- (R2) *Isomorphism invariance.*  If `f : G -> K` is an isomorphism, then
  `f(Rad(G)) = Rad(K)`.  Apply (R1) to `f` and to `f^(-1)`.
- (R3) *Subgroups.*  If `H <= G`, then `Rad(H) <= H ∩ Rad(G)`.  The
  restriction to `H` of a corona representation of `G` is a corona
  representation of `H`, so `Rad(H)` lies in the kernel of each such
  restriction.  In particular, by (U), a subgroup of an MF group is MF.

Each is a one-line consequence of the definition of `Rad` as an
intersection of kernels.

## Step 1. The radical is everything or central

Put `N = Rad(T̄)`.  It is normal in `T̄`, being an intersection of kernels.

- `p` is onto, so `p(N)` is normal in `T`.  By (I1), `p(N) = 1` or `p(N) = T`.
- *Case `p(N) = T`.*  For `g in T̄` pick `n in N` with `p(n) = p(g)`.  Then
  `g n^(-1) in ker p = <z>`, so `T̄ = N <z>`.  Since `z` is central,
  `[a b, c d] = [a, c]` for `a, c in N` and `b, d in <z>`.  So
  `[T̄, T̄] = [N <z>, N <z>] = [N, N] <= N`.  By (P1), `T̄ = [T̄, T̄] <= N`, so
  `N = T̄`.
- *Case `p(N) = 1`.*  Then `N <= <z>`.  The group `<z>` is infinite cyclic,
  because `z^m(0) = m`.  So `N = <z^m>` for a unique `m >= 0`.

## Step 2. The dilation empties the central branch

Let `h(x) = 2x` and `lambda(g) = h^(-1) g h`, so `lambda(g)(x) = g(2x)/2`.
This is `lambda^1` of (P2).  Check directly that `lambda` maps `T̄` into
itself:
- `lambda(g)(x+1) = g(2x+2)/2 = (g(2x)+2)/2 = lambda(g)(x) + 1`, so
  `lambda(g)` commutes with `z`;
- conjugating by the linear map `h` keeps slopes and halves breakpoints, so
  `lambda(g)` is piecewise linear with slopes in `2^Z` and breakpoints in
  `Z[1/2]`, finitely many mod 1;
- `h` maps `Z[1/2]` onto itself, so `lambda(g)` does too.

`lambda` is an injective homomorphism, being a restriction of conjugation in
`Homeo(R)`.  Also `lambda(z)(x) = (2x+1)/2 = x + 1/2`.  Write `t_1` for this
translation by `1/2`.  Then `t_1 in T̄` and `t_1^2 = z`.  Since `t_1^j(0) = j/2`,
`t_1` has infinite order.

Now suppose `N = <z^m>` as in the second case of Step 1.  Put `H = lambda(T̄)`.
- `lambda : T̄ -> H` is an isomorphism, so by (R2), `Rad(H) = lambda(N) = <t_1^m>`.
- By (R3), `Rad(H) <= Rad(T̄) = N = <z^m> = <t_1^(2m)>`.

So `t_1^m in <t_1^(2m)>`.  Because `t_1` has infinite order, this means
`m = 2m j` for some integer `j`, which forces `m = 0`.  Hence `N = 1`.

With Step 1 this proves **item 1**: `Rad(T̄) in {1, T̄}`.

## Step 3. Item 2 (one-word criterion)

By (U), `T̄` is not MF iff `Rad(T̄) != 1`.  By item 1 this happens iff
`Rad(T̄) = T̄`, and then `z in Rad(T̄)`.  Conversely `z != 1`, so `z in Rad(T̄)`
makes the radical nontrivial, hence equal to `T̄`.  "Some nontrivial element
lies in `Rad(T̄)`" sits between these.  `Rad(T̄) = T̄` means that every corona
representation kills every element, that is, every corona representation is
trivial.

## Step 4. Item 3 (downward transfer)

Assume `Rad(T̄) = T̄`.
- *Rotation centralizers.*  By (P2), `iota_k` maps `T̄` onto `C_T(r_k)`.  By
  (R1), `C_T(r_k) = iota_k(T̄) = iota_k(Rad(T̄)) <= Rad(C_T(r_k))`.  So
  `Rad(C_T(r_k)) = C_T(r_k)` for every `k >= 0`.
- *Thompson's `T`.*  This is the case `k = 0`: `r_0` is the rotation by `1`,
  which is the identity, and `iota_0 = p`.  Directly, `T = p(T̄) <= Rad(T)` by (R1).
- *Thompson's `V`.*  `Rad(V)` is normal in `V`, which is simple by (I1).  If
  `Rad(V) = 1`, then `V` is MF by (U), and `T <= V` (I1) is MF by (R3), which
  contradicts `Rad(T) = T != 1`.  So `Rad(V) = V`.

*The sharper contrapositive.*  Suppose `C_T(r_k)` is MF for one `k >= 0`.  By
(R1), `iota_k(Rad(T̄)) <= Rad(C_T(r_k)) = 1`, so
`Rad(T̄) <= ker iota_k = <z^(2^k)>` (P2).  This is a central subgroup, so by
the case analysis of Step 1 it is not `T̄`, and item 1 gives `Rad(T̄) = 1`.
With `k = 0`: if `T` is MF, then `T̄` is MF.

## Step 5. Item 4 (seed shape)

- *Torsion-free.*  `T̄ <= Homeo^+(R)`, and `Homeo^+(R)` is torsion-free.  If
  `f != 1` is increasing, pick `x` with `f(x) != x`, say `f(x) > x`.
  Monotonicity gives `f^(n)(x) > f^(n-1)(x) > ... > x` for all `n >= 1`.  The
  case `f(x) < x` is symmetric.  So `f^n != 1`.
- *Finitely presented.*  `1 -> <z> -> T̄ -> T -> 1` is exact with `<z> ≅ Z` and
  `T` finitely presented (I1).  So `T̄` is finitely presented by (I2).
- *Property-`(T)`-freeness.*  Steps 0--5 use only (I1), (I2), (P1), (P2) and (U).
  - (P1) and (P2) are established by direct proofs about PL homeomorphisms.
  - (U) is the generic universal-quotient theorem, which is proved for every
    countable group and carries no Kazhdan input.
  - (I1) and (I2) are classical facts about Thompson's groups and presentations.

  So if `Rad(T̄) = T̄` is ever proved without Property `(T)`, then `T̄` is a
  Property-`(T)`-free torsion-free finitely presented group with full MF
  radical. ∎

## Remarks

- The same argument applies to any central extension `1 -> <z> -> G -> Q -> 1`
  with `Q` simple, `G` perfect, `<z>` infinite cyclic, and an injective
  endomorphism `lambda` of `G` with `lambda(z)^n = z` for some `n >= 2`, where
  `lambda(z)` has infinite order.  Then `Rad(G) in {1, G}`.  The argument
  needs the centre to be infinite.  For a finite centre, `lambda = id` and
  `n = |z| + 1` already satisfy the identity, and nothing follows.  This is
  consistent with the central branch kept in
  `deligne-triple-cover-mf-radical-dichotomy`, whose centre is `C_3`.
- Step 4 needs `(P2)` only as "`iota_k` is a homomorphism onto `C_T(r_k)` with
  kernel `<z^(2^k)>`".  It never needs `C_T(r_k)` to be a subgroup of anything
  MF.
