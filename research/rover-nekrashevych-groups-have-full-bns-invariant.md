---
rg: 2
id: rover-nekrashevych-groups-have-full-bns-invariant
kind: claim
title: The BNS invariant Sigma^1 of every finitely generated Rover--Nekrashevych group is its whole character sphere
distinct_from:
  rover-nekrashevych-characters-are-sum-invariant: that describes which characters exist; this proves every one of them lies in Sigma^1.
  rover-nekrashevych-bnsr-invariants-are-full: that is the open claim for every Sigma^m together with the sphere; this is the proved case m = 1.
---

**ESTABLISHED (proof in `rover-nekrashevych-groups-have-full-bns-invariant-proof`; unreviewed).**

Let `G <= Aut(T_d)`, `d >= 2`, be a finitely generated self-similar group. Then `V_d(G)` is finitely generated, and
`Σ^1(V_d(G)) = S(V_d(G))`.

**Corollaries.**

- By Bieri–Neumann–Strebel, a normal subgroup `N` with `Γ/N` abelian is finitely generated iff `S(Γ,N) ⊆ Σ^1(Γ)`.
  So every normal subgroup of `V_d(G)` that contains `[V_d(G), V_d(G)]` is finitely generated.
  - This includes the simple commutator subgroup (Nekrashevych, arXiv:1312.5654, Theorem 4.7).
  - It also includes the kernel of every character.
- For the binary odometer, `V_2(Z)` maps onto `Z` by total `a`-exponent, and the kernel is finitely generated.

**Contrast.** For Thompson's `F` the two exceptional characters (germs at the endpoints `0` and `1`) cannot be
realized by elements supported away from the endpoints, and `Σ^1(F)` omits exactly those two points
(Bieri–Neumann–Strebel). In `V_d(G)` every character is realized by elements supported in arbitrarily small cones.
That is the whole mechanism of the proof.

**Credit and novelty.** The Σ¹ criterion is standard (see `commuting-living-generators-give-sigma-one`). The corollary
on finite generation of the commutator subgroup may follow from Nekrashevych's finite generation results for
expansive groupoids ("Simple groups of dynamical origin"); not checked. Novelty of the Σ¹ statement is unchecked:
this lane had no web search.

## Attempts

- Proved; see the proof route.
