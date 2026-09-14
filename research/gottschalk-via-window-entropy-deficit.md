---
rg: 2
id: gottschalk-via-window-entropy-deficit
kind: route
title: Compare the window entropy of an image subshift's coordinate process with the Bernoulli shift's
target: gottschalk-surjunctivity-conjecture
requires: []
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

**INVALID.** Recorded so that the most tempting entropy argument has an address,
and a kill.

## The proposed step

The image `X = tau(A^G)` of a strict automaton misses a pattern. The coordinate
process of `tau_* mu_A` then has per-site window entropy `inf_F H(beta^F)/|F|`
below `log |A|`, while the Bernoulli shift's coordinate process has exactly
`log |A|`. Since `tau` is an isomorphism, the step concludes a contradiction.

## Why it fails

Over a nonamenable group the window entropy of a generating partition is not an
invariant. `window-entropy-deficits-are-not-isomorphism-invariant` exhibits two
generating partitions of one Bernoulli shift with different values. Over amenable
groups the step is correct, and it is the classical proof.

## What replaces it

`strict-automaton-lowers-bernoulli-rokhlin-entropy` uses Rokhlin entropy instead of
window entropy and pays the marker cost by amplification. The resulting route
`gottschalk-via-maximal-bernoulli-rokhlin-entropy` needs the open claim
`bernoulli-rokhlin-entropy-maximal-for-every-group`.
