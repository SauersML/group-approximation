---
rg: 2
id: bf-n-r-pulled-back-sigma-one-misses-only-endpoint-characters
kind: claim
title: "A character of bF_{n,r} pulled back from F_{n,r} misses Sigma^1 exactly when it is an endpoint character"
distinct_from:
  bf-n-r-pulled-back-characters-follow-endpoint-hull: that open claim also asserts the Sigma^m formula for m >= 2; this claim is its m = 1 half only.
  bf-n-r-off-endpoint-plane-pullbacks-lie-in-sigma-one: that claim covers Sigma^1 off span(chi_0, chi_1); this one is the full two-sided Sigma^1 statement, including the endpoint circle.
---

For `n >= 2`, `r >= 1` and nonzero `psi` in `Hom(F_{n,r}, R)`:
`[psi o pi]` is not in `Sigma^1(bF_{n,r})` iff `[psi]` is `[chi_0]` or `[chi_1]`.
Here `chi_0`, `chi_1` are the log-slope characters at `0` and `r` (Zaremsky,
arXiv:1502.02620).

Key new step: `s(y)` commutes with the winding of a cable `I` around a cable `J`
whenever `y` maps `I` and `J` onto themselves, even if `y` is not affine on
them. So an element supported inside the first leaf centralizes every
first-leaf winding.

Unreviewed. Proof: `research/artifacts/zp-bf-n-r-sigma1-pullbacks-2026-09-20.md`.
