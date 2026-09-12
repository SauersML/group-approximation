---
rg: 2
id: kt-double-stable-vertex-mf-trace-models
kind: claim
title: The Kun--Thom double has MF-trace models with stable vertex representations
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: that asks for any MF-trace model of the double; this restricts to models whose two vertex restrictions are operator-norm close to genuine representations of G, the shape vertex matricial stability would give.
  stable-vertex-mf-trace-models-need-inequivalent-marginals: that is the established necessary shape of such models; this is their open existence.
---

**OPEN.**  For the q=2 Kun--Thom double `D = G *_Gamma G`, find pointwise
operator-norm asymptotic homomorphisms `sigma_n : D -> U(d_n)` with
`tr(sigma_n(g)) -> delta_e(g)`, and genuine representations `pi^1_n, pi^2_n` of
`G` with `||sigma_n(iota_i(g)) - pi^i_n(g)||_op -> 0`.

By `stable-vertex-mf-trace-models-need-inequivalent-marginals`, at every large
stage `pi^1_n|_Gamma` and `pi^2_n|_Gamma` must be inequivalent, with the
mismatch confined to normalized dimension `O(delta_n^2)`.

## Attempts

* **Permutation vertex models**, e.g. regular representations of finite
  quotients of `G`.  Dead: permutation corollary of the constraint claim.
* **Equal or conjugate Kazhdan marginals**, e.g. both vertices from one
  representation of `G`.  Dead: the constraint claim gives an exact model of
  the non-MAP group `D` with the same limiting traces.
* **Mismatch on extendable Clifford orbits, or any mismatch cancellable at
  cost `o(d_n)`.**  Dead: `vertex-mismatch-needs-nonextendable-clifford-orbits`.
  The Kun--Thom `Gamma` is infranormal, so its closed image is normal in every
  vertex image, and extendable orbits cancel at cost at most
  `2 (delta_n/epsilon)^2 d_n`.
* **Mismatch carried by irreducibles with a nontrivial Clifford extension class
  in `H^2(S/L_n, U(1))`, not cancellable at cost `o(d_n)`.**  The only shape
  left.  No construction yet.  Deciding whether the Theorem E vertex images
  admit such classes on inertia groups is the next test.
