---
rg: 2
id: kazhdan-groups-mean-free-amenable-iff-residually-finite
kind: claim
title: A countable group with a Kazhdan pair admits a mean-free amenable action exactly when it is residually finite, because its invariant means live on finite orbits
distinct_from:
  mean-free-amenable-actions-residually-amenable-and-sofic: that proves existence for residually amenable groups and soficity for every group with such an action; this shows that under property (T) existence is equivalent to residual finiteness.
---

**ESTABLISHED.** **Setting.**
- `G` is a countable group with a *Kazhdan pair* `(Q, κ)`: `Q ⊆ G` is finite, `κ > 0`, and every unitary
  representation of `G` with a unit vector `η` such that `max_(s ∈ Q) ‖sη - η‖ < κ` has a nonzero
  invariant vector.
- Means, invariance and mean-free amenable actions are as in
  `mean-free-amenable-actions-residually-amenable-and-sofic`.
- For a `G`-set `Ω`, `Ω_fin` is the union of the finite `G`-orbits.

**Statement.**
1. **Finite orbits carry everything.** Every invariant mean `m` on every `G`-set `Ω` has `m(Ω_fin) = 1`.
2. **Dichotomy.** `G` admits a mean-free amenable action if and only if `G` is residually finite.

**Consequences.**
- **Simple Kazhdan groups.** An infinite simple group with a Kazhdan pair has no mean-free amenable
  action. Its only finite quotient is trivial, so every finite orbit is fixed pointwise, and every
  invariant mean on every `G`-set gives `Fix(g)` mass `1`. So sofic approximations of such a group can
  never be read off from Følner sets of a genuine action, as in item 3 of the companion claim.
- **Where the notion sits.** Every residually finite group has a mean-free amenable action, and every
  group with one is sofic. Under property (T) the first implication reverses. A sofic Kazhdan group that
  is not residually finite, if one exists, would be sofic without such an action.

**Trust surface.** Elementary Hilbert-space arguments. The Kazhdan pair is taken as the definition of
property (T), with no external input. No novelty is claimed.

**Prior work.** Item 2 is Proposition 4.4 of Elek–Szabó, Math. Ann. 332 (2005), where these actions are
called essentially free amenable actions (`elek-szabo-essentially-free-amenable-actions`).

**ROUTES:** `kazhdan-mean-free-amenable-residually-finite-proof`.
