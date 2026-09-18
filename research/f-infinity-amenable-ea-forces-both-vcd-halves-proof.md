---
rg: 2
id: f-infinity-amenable-ea-forces-both-vcd-halves-proof
kind: route
title: "Proof: apply the KMN type VF and virtual solubility theorems to an elementary amenable F_infinity group"
target: f-infinity-amenable-ea-forces-both-vcd-halves
requires:
  - elementary-amenable-f-infinity-groups-are-type-vf
  - elementary-amenable-fp-infinity-groups-virtually-soluble
---

Assume every amenable group of type `F_∞` is elementary amenable.

**Half 1: finite vcd.** Let `G` be amenable of type `F_∞`. By assumption `G` is
elementary amenable.

- By `elementary-amenable-f-infinity-groups-are-type-vf`, some `H ≤ G` of finite
  index has a finite `K(H,1)` complex `L`.
- The cellular chain complex of the universal cover of `L` is a free resolution of
  `Z` over `ZH` of length `dim L`. So `cd H ≤ dim L < ∞`. This is step 2 of
  `elementary-amenable-stable-bnsr-via-type-vf`.

So `G` has finite vcd.

**Half 2: the finite-cd case.** Let `G` be amenable of type `F_∞` with `cd G < ∞`.

- By assumption `G` is elementary amenable.
- Type `F_∞` implies type `FP_∞`: the cellular chains of the universal cover of a
  `K(G,1)` with finitely many cells in each dimension are a free resolution of finite
  type.
- By `elementary-amenable-fp-infinity-groups-virtually-soluble`, `G` is virtually
  soluble. ∎

The hypothesis `cd G < ∞` is not used in Half 2. The conclusion there is the
stronger statement "every amenable `F_∞` group is virtually soluble". Half 2 is
stated with the finite-cd hypothesis because the decomposition only needs that case.
