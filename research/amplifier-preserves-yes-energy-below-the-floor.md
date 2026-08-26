---
rg: 2
id: amplifier-preserves-yes-energy-below-the-floor
kind: claim
title: The amplified Hamiltonian keeps YES-instance energy strictly below the NO-instance floor
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

The completeness half of the attack.  For the reduction of
`locality-preserving-constant-combinatorial-gap`, a YES instance yields

```text
lambda_min(H'_YES) <= a  <  beta/C,                             (YES1)
```

where `beta` is the combinatorial gap of (LPC1) and `C` the rounder constant
of `amplified-hamiltonian-has-a-constant-cost-rounder`.  Without (YES1) the
NO-side floor `beta/C` is a bound with nothing on the other side of it and
the promise gap is empty.

The requirement is quantitative, not qualitative: an amplifier which
preserves a YES witness only up to energy density `beta/C` or above produces
no promise gap however good its soundness is.  So `a`, `beta` and `C` must be
tracked jointly through the amplification, and the honest reading of the
criterion is that the three constants are one constant.

## Attempts

- **Assume the amplifier is gap-preserving on the YES side by construction.**
  Not available: the amplification template announced in July 2026 is
  described only through its effect on the combinatorial gap, and the
  combinatorial gap is a NO-side notion.  A YES witness is a low-energy
  state, not an exactly-satisfying one, so it is not the object the
  combinatorial statement talks about.
- **Absorb the loss into the constant.**  Circular here: the loss is measured
  against `beta/C`, and `C` is exactly what the exactification argument is
  trying to bound.  Deferred until either `beta` or `C` is pinned by an
  explicit construction.
