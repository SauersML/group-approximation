---
rg: 2
id: bounded-exponent-fg-group-residual-has-finite-index
kind: claim
title: A finitely generated group of bounded exponent has a finite-index subgroup with no proper finite-index subgroups
distinct_from:
  fg-rf-bounded-exponent-groups-are-finite: that says a residually finite group of bounded exponent is finite; this applies it to the finite residual of an arbitrary one, which gives a finite-index perfect subgroup with no finite quotients and an infinite simple quotient when the group is infinite
---

Let `G` be finitely generated with `g^N = 1` for all `g in G`, and let `K`
be the finite residual of `G`, the intersection of its finite-index normal
subgroups. Then:

1. `K` has finite index in `G`.
2. `K` has no proper subgroup of finite index. In particular `K` is perfect.
3. If `G` is finitely presented, so is `K`.
4. If `G` is infinite, `K` is infinite and has an infinite simple quotient of
   exponent dividing `N`.

**For Zaremsky Problem 1.11.** A finitely presented infinite torsion group of
bounded exponent exists if and only if a finitely presented infinite group
of bounded exponent with no proper finite-index subgroup exists. Its
profinite completion is finite.

This applies to the construction route
`fp-torsion-via-olshanskii-sapir-coinvariants`. Suppose the coinvariant group
`H̄_{phi^m}` of `olshanskii-sapir-hnn-has-infinite-coinvariants` is infinite.
It is finitely presented, as a finite-index subgroup of
`𝒢/<<t^m>>`, and has exponent `n`. So it contains a finitely presented,
perfect, infinite subgroup of finite index, of exponent `n`, with no proper
finite-index subgroup, which maps onto an infinite simple group of exponent
`n`. Any attempt to show the coinvariants are infinite must therefore produce
infinite quotients that no finite quotient detects. Counting finite quotients
cannot certify infinitude on this route.

**Model tests.**
- A finite group: `K = 1`, which satisfies 1, 2 and 3; 4 does not apply.
- A Tarski monster of exponent `p`, which is infinite and simple: `K = G`.
- Infinite free Burnside groups `B(m,N)`: `G/K` is the restricted Burnside
  group `R(m,N)`, finite as `restricted-burnside-finiteness` says.

Proof: `bounded-exponent-fg-group-residual-has-finite-index-proof`.
