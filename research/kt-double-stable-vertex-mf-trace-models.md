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
* **Non-permutation finite-image vertex representations with an
  `O(delta_n^2)` Kazhdan multiplicity mismatch.**  The only shape left.  No
  construction yet.  It needs a mismatch that no `o(d_n)`-dimensional pair of
  representations of `G` can cancel, since cancelling it would again produce an
  exact model.
