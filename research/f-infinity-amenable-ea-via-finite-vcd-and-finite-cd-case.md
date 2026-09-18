---
rg: 2
id: f-infinity-amenable-ea-via-finite-vcd-and-finite-cd-case
kind: route
title: "Amenable F_infinity groups are elementary amenable iff they have finite vcd and the finite-cd ones are virtually soluble"
target: every-f-infinity-amenable-group-is-elementary-amenable
requires:
  - amenable-f-infinity-groups-have-finite-vcd
  - amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble
---

**Sufficiency.** Let `G` be amenable of type `F_∞`.

1. By `amenable-f-infinity-groups-have-finite-vcd`, some `H ≤ G` of finite index
   has `cd H < ∞`.
2. `H` is amenable, since subgroups of amenable groups are amenable. It is of type
   `F_∞`: a finite-index subgroup of a group of type `F_∞` is of type `F_∞`, because
   the finite-sheeted cover of a `K(G,1)` with finitely many cells in each dimension
   is a `K(H,1)` with finitely many cells in each dimension.
3. By `amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble`, `H` has a
   soluble subgroup `S` of finite index. Then `[G:S] < ∞`.
4. The normal core `S_0 = ∩_g gSg^{-1}` has finite index and is soluble. `G/S_0` is
   finite. Chou's class `EG` contains the finite and the abelian groups and is
   closed under extensions. So `S_0 ∈ EG` (by induction on derived length), and then
   `G ∈ EG`. ∎

**Necessity.** `f-infinity-amenable-ea-forces-both-vcd-halves` shows
that the target implies both prerequisites. So this route is an equivalence, not
just a sufficient condition.

**Why this is a decomposition into halves that can fail independently.**

- A counterexample to the target with infinite vcd refutes the first half only. This
  is what Grigorchuk's HNN extension would be if it is of type `F_∞`, and what
  Thompson `F` would be if amenable.
- A counterexample with finite vcd refutes the second half only. It would also answer
  Kropholler's question `amenable-groups-of-finite-cd-are-virtually-solvable`
  negatively.
- The first half contains `thompson-f-is-not-amenable`
  (`thompson-f-not-amenable-via-finite-vcd-of-amenable-f-infinity`). The second half
  never mentions an infinite-dimensional group.
- Tools belong to one side each. Rational-cd monotonicity (Sauer, Gandini) and
  torsion work only on the first half. Kaplansky / zero-divisor, `L²` Euler
  characteristic and BNSR methods (Degrijse) work only on the second, where type
  `FP` is available.
