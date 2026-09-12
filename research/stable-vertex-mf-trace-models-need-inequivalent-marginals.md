---
rg: 2
id: stable-vertex-mf-trace-models-need-inequivalent-marginals
kind: claim
title: MF-trace models of a non-MAP Kazhdan double with stable vertices need inequivalent Kazhdan marginals
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: that is the open MF-trace target for the Kun--Thom double; this is a necessary shape for every witness whose vertex restrictions are close to genuine representations.
  kt-double-canonical-vertex-marginals-admit-large-amalgam-twists: that builds exact vertex representations with regular characters agreeing exactly on Gamma; this proves the opposite shape is forced once the traces of all mixed words must vanish.
---

ESTABLISHED.  Let `Gamma <= G` with `Gamma` Kazhdan, put `D = G *_Gamma G`,
and assume `D` is not maximally almost periodic.  Examples: `D` finitely
generated and not residually finite; in particular `D` nonsofic.  Suppose
`sigma_n : D -> U(d_n)` are pointwise operator-norm asymptotic homomorphisms
with `tr(sigma_n(g)) -> delta_e(g)`, and that genuine representations
`pi^1_n, pi^2_n` of `G` satisfy

```text
||sigma_n(iota_i(g)) - pi^i_n(g)||_op -> 0        (g in G, i = 1, 2).
```

Then for all but finitely many `n` the restrictions `pi^1_n|_Gamma` and
`pi^2_n|_Gamma` are **not** unitarily equivalent.

**Permutation corollary.**  No such models exist when the `pi^i_n` are
permutation representations; this part needs only that `Gamma` is finitely
generated.

So any MF-trace witness for the Kun--Thom double with stable vertex models must
carry a genuinely inequivalent Kazhdan marginal at every large stage.  By the
proof, its normalized dimension is at most `(delta_n/epsilon)^2`, where
`delta_n` is the operator-norm identification defect on a Kazhdan set.
Finite-quotient permutation models are excluded outright.
