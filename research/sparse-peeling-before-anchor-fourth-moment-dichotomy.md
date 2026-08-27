---
rg: 2
id: sparse-peeling-before-anchor-fourth-moment-dichotomy
kind: claim
title: Peel or cheaply repair sparse sites before applying anchor fourth-moment contraction
refuted_by: translated-three-site-blocks-defeat-global-peeling
distinct_from:
  all-dual-unique-neighbors-contract-operator-tails: that supplies a scalar tail recurrence down to a bad-row floor; this asks to turn its sparse output into a same-Hilbert repair and then prove the fourth-moment gain on the shortened diffuse core.
  sparse-anchor-odd-fourth-moment-is-the-renormalization-gate: that asserted a little-o estimate directly on the unpeeled common low block and is refuted by a three-site Pauli block.
  balanced-overlay-common-reducing-outlier-cut: that removes a physical Hilbert-space projection; this requires a coordinate-site peeling/repair, since the localized Pauli obstruction is full rank.
---

**Refuted in its global-set formulation.**  Given balanced energy `E`, produce a coordinate set `U` and corrected
reflections `(Q_i')` such that

```text
 |U|/L + avg_i ||Q_i-Q_i'||_2^2 <=o_E(1),               (SPF1)
```

all sparse anchor-odd spikes are supported on or charged to `U`, and on the
shortened tuple outside `U` the two-odd-factor face remainder satisfies a
dimension-free little-o estimate relative to its anchor energy.  Combining
that dichotomy with `one-anchor-grading-makes-parity-damage-quadratic` and
the exact code-distance anchor gap would give strict expected contraction.

## Attempts

`all-dual-unique-neighbors-contract-operator-tails` is the correct first
step: it contracts small scalar coordinate tails to the bad-row floor, and
the three-site counterexample lies entirely in the sparse side which that
procedure is designed to expose.  Merely deleting the exposed coordinates
is cheap in the averaged generator metric.

What remains unproved is compatibility with the overlapping occurrence
presentation.  Resetting a shared coordinate changes every incident face;
one must either repair those boundedly many clouds with total cost charged
to the deleted-site density, or shorten the local code while preserving the
uniform code-distance/conjugation gap needed by the anchor step.  Moreover,
scalar tail control does not automatically put all anchor-dependent high
spectral projections on one coordinate set.  A successful proof needs an
operator-valued stopping/assignment lemma or a local repair map whose cost
is bounded by the all-dual bad-row floor.

The central mixture in `translated-three-site-blocks-defeat-global-peeling`
makes the sparse location depend on the reducing block.  No `o(L)` global
set captures a positive fraction of the spikes, although resetting three
coordinates separately on each central block has total cost `O(1/L)`.
Thus `(SPF1)` asks for too much coherence.  The corrected target is
`central-adaptive-peeling-or-noncentral-stopping`.
