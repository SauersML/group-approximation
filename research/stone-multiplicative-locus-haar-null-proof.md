---
rg: 2
id: stone-multiplicative-locus-haar-null-proof
kind: route
title: Count ultrafilters in finite Boolean subalgebras and disintegrate regular corners over additive Haar
target: stone-multiplicative-locus-is-haar-null-in-additive-dual
requires: []
---

Every nonzero element of the discrete abelian group `K` has zero canonical
group trace, which gives `(SML2)`.  A finite Boolean algebra with `n` atoms is
`F_2^n` additively.  Its additive dual has `2^n` elements, whereas its Boolean
homomorphisms to `F_2` are precisely evaluation at one of the `n` atoms.
Restriction of Haar measure to this finite quotient is uniform.  Atomlessness
allows partitions with arbitrarily many atoms, proving `(SML4)` and
`m(S)=0`.

The Stone representation theorem identifies the clopen selected by `a` with
`{epsilon:epsilon(a)=1}`.  Since `p_a=(1-u_a)/2` is its indicator on `S`,
integration gives `(SML5)`.

Choose right-coset representatives for `K` in `G`.  Then
`ell^2(G)` restricted to the left `K`-action is a direct sum of copies of
`ell^2(K)`, so its spectral type is additive Haar.  A reducing projection
`q` gives a normal functional on `L(K)`; explicitly
`tau(q lambda(k))/tau(q)` has Radon--Nikodym density
`E_(L(K))(q)/tau(q)`.  This proves the absolute-continuity assertion for
`(SML6)` and excludes `(SML5)`.

Finally, a group quotient maps `K` to `K/N`; its nonidentity elements retain
zero canonical trace.  Expanding `(SML7)` gives a nontrivial linear relation
among `1,u_a,u_b,u_(a symmetric_difference b),u_(a meet b)`, not a group-word
identity.  This proves the relator and central-corner fence.

