---
rg: 2
id: two-transitive-infinite-action-is-finite-dimensionally-codense
kind: claim
title: In a finite-dimensional unitary representation of a group acting 2-transitively on an infinite set, stabilizer-fixed vectors are fixed
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  approximate-gram-data-certifies-only-inverse-square-dimension: that bounds what approximately equal inner products can force; this uses exactly equal inner products, supplied by a group symmetry, to force infinitely many unit vectors in finite dimension to coincide.
---

Let `G` act 2-transitively on an infinite set `Y`, let `G_0` be a point
stabilizer, and let `pi` be a finite-dimensional unitary representation of
`G`.  Then every `G_0`-fixed vector is `G`-fixed:

```text
pi^(G_0) = pi^G.                                                 (TC1)
```

*Proof.*  Let `v` be a unit vector fixed by `G_0` and put
`v_y = pi(g)v` for any `g` with `g.0 = y`; this is well defined.  For
`y != y'` pick `h in G` with `h.(0, g_1.0) = (y, y')`; then
`<v_y, v_(y')> = <v_0, v_(g_1.0)> =: c` is independent of the pair.  The
Gram matrix of `N` of the `v_y` is `(1-c)I + cJ`, of rank at least `N-1`
unless `c = 1`; since the rank is at most `dim pi` and `N` is arbitrary,
`c = 1`, so all `v_y` coincide and `v` is `G`-fixed. ∎

The conclusion is false for infinite-dimensional representations
(`l^2(G/G_0)` has the `G_0`-fixed vector `delta_(G_0)`), which is exactly
where the regular representation escapes the argument, as it must by
`regular-trace-blocks-exact-local-predicate-return`.

More generally `(TC1)` holds whenever the orbitals of `G` on `Y` are
finitely many and the resulting class function has no finite-dimensional
matrix-coefficient component, and it holds for pairs such as
`SL_3(Z) <= SL_3(Z[1/p])` by strong approximation (every finite quotient of
the big group is already the image of the small one), without any
transitivity.  Call a pair `(G, G_0)` satisfying `(TC1)` for all
finite-dimensional unitary `pi` **finite-dimensionally co-dense**.  It
forces `[G : G_0] = infinity` (else `l^2(G/G_0)` is a finite-dimensional
counterexample).

This is the input that `pauli-lamplighter-over-stable-codense-kazhdan-pair`
uses in place of every Pauli dimension bound: infinitely many exact
conjugates cannot be distinct in finite dimension.
