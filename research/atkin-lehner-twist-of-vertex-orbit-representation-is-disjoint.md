---
rg: 2
id: atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint
kind: claim
artifacts:
  - research/artifacts/atkin_lehner_tv.py
title: The Atkin--Lehner twist of a vertex-orbit representation of Gamma_0(p^2k) shares only its unipotent-trivial constituents
distinct_from:
  homogeneous-quotient-near-genuine-microstates-are-deep: that is the rank-two (T) descent theorem bounding depth and level weights of near-genuine microstates; this is an exact rank-one computation of the isotypic mismatch that the same matching condition imposes on a single congruence level.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open embeddability question; this is an unconditional finite-group theorem quantifying one obstruction on its congruence exact face.
---

**THEOREM (established here; proof in
`atkin-lehner-vertex-orbit-tv-proof`, numerically verified for
`p in {2,3,5,7,11}`, `k <= 3`).**  Let `C = SL_2(Z)`, `h = diag(p, p^-1)`, and identify the
Bruhat--Tits tree of `SL_2(Q_p)` with homothety classes of lattices,
`o = [Z_p^2]`.  Then

```text
C cap h^-1 C h = Gamma_0(p^(2k))-type:  C^((k)) := cap_(0<=i<=k) h^-i C h^i = Gamma_0(p^(2k)),
g_k := J^-1 h^k = [[0, p^-k], [-p^k, 0]]   (J = [[0,-1],[1,0]] in C)
```

normalizes `Gamma_0(p^(2k))` (`g_k` is the Atkin--Lehner involution,
`Ad(g_k): [[a,b],[c,d]] |-> [[d, -c/p^(2k)], [-p^(2k) b, a]]`) and swaps the
vertices `o` and `v_(-k) = h^-k o` at distance `2k`.  The sphere `S(o,2k)`
is the `C`-orbit of `h^k o`, identified with `P^1(Z/p^(2k))`; its far part
`X = {[x:1]}` (geodesic from `o` not starting toward `v_(-k)`) has
`p^(2k)` points, its near part `p^(2k-1)`.  Let `sigma` be the permutation
representation of `Gamma_0(p^(2k))` on `S(o,2k)` (Moebius action), `sigma^g`
its `Ad(g_k)`-twist (the permutation representation on the sphere
`S(v_(-k), 2k)`), and likewise `sigma_X`, `sigma_X^g` for the far part.  Let
`w(.)` denote isotypic weight measures (`w(pi) = dim(pi) mult(pi) / dim`).
Then:

```text
TV( w(sigma_X), w(sigma_X^g) )  =  2 - 2 p^(-2k),                     (AL1)
TV( w(sigma),   w(sigma^g) )    =  2 - 2 p^(-k).                      (AL2)
```

Concretely: the kernels of the two actions generate the normal subgroup
`N = {a = d = +-1 mod p^(2k)}` of `Gamma_0(p^(2k))`, so a constituent common
to a vertex-orbit representation and its twist must be trivial on all
unipotents and is a character of `a mod p^(2k)`; on the far sphere only the
trivial representation survives, and on the whole sphere the shared weight
is `(1 + p^k + p^(k-1) - 1)/|S| = p^-k`.  On the twisted side the far action
is **affine**, `x |-> (d x - c/p^(2k))/a`, using the entry `c` modulo
`p^(4k)`: the twist reads the second congruence digit of the lower-left
entry, which the untwisted action cannot see, and vice versa for `b`.

**Role.**  On the congruence exact face of
`relative-commutant-collapse-for-sl2-pair` (microstates of
`SL_2(Z[1/p])` whose `SL_2(Z)`-part is a genuine congruence representation
`rho'`), Step 3--4 of `homogeneous-quotient-deep-tower-proof` apply with
property `(tau)` of `Gamma_0(p^(2k))` in place of `(T)` (the intertwining
representation on Hilbert--Schmidt space factors through a congruence
quotient), so the weight measure of `Res_(Gamma_0(p^(2k))) rho'` must be
within `O(k epsilon/kappa_tau)` of its Atkin--Lehner twist for every `k` up
to the depth.  `(AL1)`--`(AL2)` say that each single vertex-orbit level is
maximally far from that: a nearly symmetric tower must pair every
vertex-orbit level with the levels carrying its twisted constituents (the
sphere `S(v_(-k),2k)` is a union of `Gamma_0(p^(2k))`-orbits inside
`S(o, 2k+2j)`, `0 <= j <= 2k`), which is the top-heaviness recorded on
`sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`.  The
statement is about congruence representations only: `SL_2(Z)` has
non-congruence finite quotients, on which `(tau)` gives no spectral gap and
isotypic weights are not stable under perturbation, so the rank-one
exact face is larger than its congruence part.  The rank-two analogue
(`C_0 = SL_3(Z) cap h^-1 SL_3(Z) h`, `g = J^-1 h` for a Weyl element `J`)
has the same kernel structure and needs no `(tau)` caveat by the congruence
subgroup property; its constants are not computed here.
