---
rg: 2
id: thompson-v-covariant-cantor-representations-are-not-amenable
kind: claim
title: No covariant representation of the Cantor system of Thompson's V is Bekka-amenable
distinct_from:
  thompson-v-cantor-orbits-have-no-folner-sets: that treats finite point sets, the permutation case; this treats every unitary representation carrying a covariant copy of C(Cantor), including Koopman representations and their finite-rank compressions.
---

**ESTABLISHED.** Let `pi` be a unitary representation of `V` on `H`, and
`rho: C(X) -> B(H)` a unital `*`-homomorphism from the continuous functions on
the Cantor set with `pi(g) rho(f) pi(g)^* = rho(f o g^(-1))`. Then `pi` is not
amenable in Bekka's sense.

Bekka amenability is the existence of nonzero finite-rank projections `P` with
`||pi(g) P pi(g)^* - P||_2 / ||P||_2 -> 0` for every `g`. Those are exactly the
projections whose compressions `P pi(g) P` are normalized-HS almost
representations. So no HS model of `V` is a compression of a covariant
representation, whatever measure class it comes from. The Koopman
representation on `L^2(X, mu)` with Radon--Nikodym factors is one example.
Tracial cylinder models, orbit truncations and Koopman compressions all fail
for the same reason.

Proof: amenability gives a state `Phi` on `B(H)` invariant under conjugation
by `pi`. Then `Phi o rho` is a `V`-invariant state on `C(X)`, that is, a
`V`-invariant probability measure. The halving argument of
`thompson-v-cantor-orbits-have-no-folner-sets-proof` rules that out.
