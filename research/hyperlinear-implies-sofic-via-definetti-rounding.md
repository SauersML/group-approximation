---
rg: 2
id: hyperlinear-implies-sofic-via-definetti-rounding
kind: route
title: Balanced amplification feeds an assignment-side dimension-free symmetric-extension rounding theorem
target: hyperlinear-implies-sofic
requires:
  - definetti-group-table-rounding
  - balanced-replica-hs-amplification
---

Let `G` be hyperlinear, fix a finite window `F` and `eps>0`, and let `T` be its
partial multiplication table. Choose the extension level and threshold supplied
by `definetti-group-table-rounding`.

Hyperlinearity supplies unitary microstates of `T` at arbitrarily small HS and
regular-trace error. `balanced-replica-hs-amplification` permits whatever fixed
number of phase-free replicas the table encoding needs while keeping the
multiplicative error arbitrarily small: after `m` balanced copies the squared
error grows by at most a factor `2m`, and nontrivial trace magnitudes are
raised to the `2m` power.

Now invoke **the lift clause of `definetti-group-table-rounding`** to build its
assignment/context-side symmetric extension and apply that theorem's rounding
conclusion. This distinction is essential: the route does *not* infer
classicality merely because the raw balanced replicas are exchangeable;
`replica-definetti-saturation-no-go` shows those independent replicas are
already product across the wrong split. The hypothetical table theorem must
construct and classicalize the internal assignment variables.

Its endpoint is a multiplicative Markov or permutation model of `T` with error
`<eps`; in the Markov formulation `markov-sofic-equals-sofic` supplies the final
integrality. Since `F,eps` were arbitrary, `G` is sofic.
