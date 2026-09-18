---
rg: 2
id: sft-irreducible-core-iff-unique-recurrent-component
kind: claim
title: A subshift of finite type without isolated points or empty cones has an irreducible core exactly when its graph has a single strongly connected component containing a cycle
distinct_from:
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1; this is the graph-theoretic form of its remaining obstacle (ii), for the atom-type graph of a hyperbolic group.
  free-products-of-hyperbolic-groups-are-contracting-rsgs: that verifies the irreducible core for free products geometrically; this says what has to be verified in general.
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

**ESTABLISHED** (lane `bh-free-23`, lane proof, elementary, not independently reviewed; no priority
claimed; the proof is below).

## Statement

Let `Γ` be a finite directed graph such that `Σ_Γ` has no isolated points and no empty cones
(BBMZ arXiv:2309.06224v3, `ssec:subshifts`). Call a strongly connected component of `Γ`
*recurrent* if it contains a directed cycle. Then:

- `Σ_Γ` has an irreducible core (BBMZ definition, conditions (i)–(iii)) **if and only if** `Γ`
  has exactly one recurrent component;
- in that case the core is that component, and it is a sink: no edge leaves it.

## Consequence for BBMZ-hyperbolic Question 1.1

- **The obstacle, restated.** For a hyperbolic group `G` whose horofunction boundary has no
  isolated points, obstacle (ii) is exactly this: the atom-type graph must have a single
  recurrent component. Every atom type must eventually feed into one class of atom types that
  recur along geodesic rays.
- **The other hypotheses are automatic.** The type graph never has empty cones, since every
  infinite atom has an infinite child. The no-isolated-points condition is then the one other
  hypothesis, and it also rules out a single-cycle core.

## Proof

- **Every node reaches a cycle.** No empty cones means every node has an infinite outgoing path.
  Such a path repeats a node, so it contains a directed cycle.
- **(⇒) Every cycle lies in the core.** Let `Γ_0` be an irreducible core with constant `N`. For a
  cycle `c` and a node `x` on it, the path `c^k` rotated to start and end at `x` has length at
  least `N` for large `k`, so by (iii) it ends at `x ∈ Γ_0`. So every cycle lies in `Γ_0`.
- **(⇒) The core is the recurrent component.** `Γ_0` is strongly connected, so it lies in one
  component `S_0`. Every node of `S_0` lies on a cycle: `S_0` contains a cycle, since `Γ_0` is
  irreducible. So `S_0 ⊆ Γ_0`. Hence `Γ_0 = S_0`, and it is the only recurrent component, since
  every cycle lies in it.
- **(⇐) The recurrent component is a sink.** Let `S` be the unique recurrent component. If an
  edge ran from `S` to a node `u ∉ S`, then `u` would reach a cycle, which lies in `S`. So `u`
  and `S` would reach each other, and `u ∈ S`. So `S` is a sink.
- **(⇐) Conditions (ii) and (iii).** Every node reaches a cycle, hence reaches `S`: condition (ii).
  A path of length `N = |V(Γ)|` repeats a node, so it contains a cycle and meets `S`. It then
  stays in `S`: condition (iii).
- **(⇐) Condition (i).** `S` is strongly connected. It is not a single directed cycle: otherwise
  every infinite path would eventually wind around that cycle. Then `Σ_Γ` would be countable,
  since each point is determined by a finite prefix together with an eventual winding. A
  nonempty compact metrizable space without isolated points is uncountable, so this is a
  contradiction. ∎
