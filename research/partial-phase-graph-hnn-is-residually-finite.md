---
rg: 2
id: partial-phase-graph-hnn-is-residually-finite
kind: claim
title: Partial phase-graph HNNs over a fixed free coordinate are residually finite
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  graph-endomorphism-phase-hnn-embeds-formanek-procesi: that treats one injective phase map which extends to an endomorphism of the full ambient free factor; this permits two arbitrary, possibly noninjective maps defined only on a finitely generated proper subgroup and proves residual finiteness directly.
  finite-free-phase-product-embedding-has-an-injective-coordinate: that supplies a faithful coordinate and leaves nonextendable partial graph maps as the surviving case; this closes every such partial graph HNN when the faithful coordinate is retained at both ends.
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that assumes finite associated subgroups; the subgroup here can be a nonabelian finite-rank free group.
---

Let `L` be a finite-rank free group, let `A<=L` be finitely generated, let
`P` be a finitely generated residually finite group, and let
`Theta_0,Theta_1:A -> P` be arbitrary homomorphisms.  In `L times P` put

```text
G_nu={(a,Theta_nu(a)):a in A},             nu=0,1.       (PPG1)
```

Then the HNN extension

```text
E=<L times P,t |
 t(a,Theta_0(a))t^(-1)=(a,Theta_1(a)), a in A>          (PPG2)
```

is residually finite.  No `Theta_nu` need be injective or extend from `A` to
`L`; both maps may use arbitrarily many commuting phase factors by taking
their direct product as `P`.

Consequently a finite-layer signed-Hecke transport cannot become decisive by
choosing a faithful phase coordinate and attaching arbitrary nonextendable
partial graph data to it while leaving that coordinate unchanged.  A live
edge must change the faithful coordinate itself, cease to have a common
faithful free coordinate at its two ends, or leave this finite-product graph
geometry.
