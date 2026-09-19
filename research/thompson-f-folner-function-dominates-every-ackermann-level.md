---
rg: 2
id: thompson-f-folner-function-dominates-every-ackermann-level
kind: claim
title: The Følner function of Thompson's group F eventually dominates every primitive recursive function
distinct_from:
  thompson-f-folner-function-exceeds-every-tower: that is Moore's theorem, beating every fixed tower exp_p; this asks for beating every Ackermann level, i.e. every primitive recursive function, which the log-height sharpness result shows Moore's method cannot reach.
  folner-functions-of-fp-amenable-groups-have-no-recursive-bound: that asks for a family of finitely presented amenable groups beating every recursive bound; this is a single group, and by Cavaleri a single amenable finitely presented group has a recursive Følner function, so only the primitive recursive threshold is at stake here.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that concerns Ramsey-function amplification; this concerns the Følner function itself.
---

**OPEN.** For the generating set `Γ = {x0^±1, x1^±1}`, and hence for every finite generating
set, the function
`Føl_{F,Γ}(N) = min{ |A| : A ⊆ F is 1/N-Følner with respect to Γ }`
eventually dominates every primitive recursive function. Here `min ∅ = ∞`.

**Trivial case.** If `F` is not amenable, then `Føl_F(N) = ∞` for large `N`, and the claim holds.
So the content of the claim is conditional on amenability.

**Why it matters.**
- *If `F` is amenable,* the claim answers negatively, for the group `F`, the question Moore
  quotes as Question 1.2 of arXiv:0905.1118v7:
  > Is there a primitive recursive function which eventually dominates every Følner function of
  > an amenable finitely presented group?
- By the w10 spark on the swarm-0917 bus, the Følner `Π2` sentence for `F` would then be
  unprovable in `IΣ1` and in any theory whose provably total functions are primitive recursive.
- Every explicit Følner family for `F` would have to be defined by a non-primitive-recursive
  recursion.
- *If false,* `F` is amenable and has Følner sets whose size is bounded by some `Ack_k(N)`.

**Status of the method.**
- By `marginal-derivative-amplification-is-sharp-at-log-height`, Moore's amplification gives
  height exactly `Θ(log N)`. So any proof along his lines must come from faster contraction,
  not from more height.
- The route `thompson-f-ackermann-folner-via-tree-derivative-hierarchy` reduces the claim to
  `thompson-f-trees-carry-an-ackermann-derivative-hierarchy`.
