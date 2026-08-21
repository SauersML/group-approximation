---
rg: 2
id: llp-implies-weak-ucp-stability
kind: claim
title: The local lifting property of the full group C*-algebra implies weak ucp-stability
distinct_from:
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that combines this implication with the non-RF Kazhdan equivalence to get non-hyperlinearity; this is the bare literature implication, factored out so that the residually finite consumers (the Dogon central-extension route) can also require it.
  kazhdan-weak-ucp-stability-is-flexible-stability: that upgrades weak ucp-stability to flexible stability using property (T); this produces weak ucp-stability from a lifting property and involves no property (T).
---

**THEOREM (Ioana--Spaas--Wiersma; see Dogon).**  Let `Gamma` be a countable
group whose full group C*-algebra `C^*(Gamma)` has Kirchberg's local
lifting property (LLP).  Then `Gamma` is weakly ucp-stable in the sense of
Dogon arXiv:2211.10492 Definition 1.5: every hyperlinear approximation
`phi_n : Gamma -> U(d_n)` is pointwise asymptotic in normalized
Hilbert--Schmidt norm to compressions `P_n pi_n(.) P_n` of genuine unitary
representations `pi_n` on Hilbert spaces containing `C^(d_n)`.

Consequences already in the graph: with non-residual-finiteness and
property (T), non-hyperlinearity
(`llp-non-rf-kazhdan-group-is-non-hyperlinear`); with property (T) alone,
flexible HS-stability on hyperlinear approximations
(`kazhdan-weak-ucp-stability-is-flexible-stability`).  Every amenable
group is weakly ucp-stable this way (Choi--Effros lifting), which is
Dogon's separation of weak ucp-stability from flexible HS-stability.
