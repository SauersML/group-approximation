---
rg: 2
id: amplifier-preserves-yes-energy-below-the-floor
kind: claim
title: The amplified Hamiltonian keeps YES-instance energy strictly below the NO-instance floor
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

The completeness half of the attack.  For the reduction of
`locality-preserving-constant-combinatorial-gap`, a YES instance yields

```text
lambda_min(H'_YES) <= a,       beta/C - a >= epsilon > 0,       (YES1)
```

where `beta` is the combinatorial gap of (LPC1) and `C` the rounder constant
of `amplified-hamiltonian-has-a-constant-cost-rounder`. The constants,
including the positive margin `epsilon`, are uniform and refer to this
same reduction. Without (YES1) the
NO-side floor `beta/C` is a bound with nothing on the other side of it and
the promise gap is empty.

The requirement is quantitative, not qualitative: an amplifier which
preserves a YES witness only up to energy density `beta/C` or above produces
no promise gap however good its soundness is.  So `a`, `beta` and `C` must be
tracked jointly through the same amplification. A pointwise strict
inequality whose margin vanishes with instance size does not suffice.

**2026-09-11: this claim is equivalent to the root.** Read, as intended, for
one reduction that also carries (LPC1) and a constant rounder, this claim
implies `quantum-pcp-constant-gap-local-hamiltonian` through
`qpcp-from-anchored-amplifier`. Conversely, a shifted root witness satisfies
it (`yes-margin-criterion-from-quantum-pcp`). The other requirements of the
anchored route are satisfied by the shifted standard reduction, whose margin
is inverse polynomial (`anchored-criterion-components-are-shift-satisfiable`).
So all promise content of the anchored attack sits here, and a proof of this
claim is a proof of quantum PCP.

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
