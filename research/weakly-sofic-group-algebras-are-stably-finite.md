---
rg: 2
id: weakly-sofic-group-algebras-are-stably-finite
kind: claim
title: Weakly sofic groups have stably finite group algebras over every finite field
distinct_from:
  linear-sofic-group-algebra-is-stably-finite: that derives stable finiteness from linear soficity through a rank ultraproduct; this asks for it from weak soficity, where the finite models carry a length and no rank.
  weakly-sofic-groups-are-surjunctive: that is the full nonlinear statement; this is its linear shadow, which it implies through stable-finiteness-failure-refutes-surjunctivity.
refuted_by:
  - clifford-cover-anti-half-skew-ring-not-directly-finite
artifacts:
  - research/artifacts/metric-ultraproduct-bounded-width-closure-2026-09-12.md
---

**OPEN.** Let `G` be weakly sofic and `F_q` a finite field. Then `F_q[G]` is stably finite: `BA = I_n` implies
`AB = I_n` for all `A, B` in `M_n(F_q[G])`.

**Routes in.** `weak-sofic-stable-finiteness-from-surjunctivity` derives it from `weakly-sofic-groups-are-surjunctive`.
That in turn is equivalent to `metric-ultraproducts-of-finite-groups-are-surjunctive`.

## Attempts

- **The rank calibration transfers only through representations** (artifact, Section 3.2, Proposition 3.1).
  - *What the proof uses.* The stable-finiteness proof for linear sofic groups consumes a Sylvester rank that is
    small on the defects.
  - *When it transfers.* Only when representation ranks dominate the lengths of the finite models in both
    directions. The subgroup is then linear sofic.
  - *Beyond that.* A finite group with an invariant length supplies no rank, and nothing on record replaces it.
- **Test host.** The Kun–Thom Clifford cover `E_S` is weakly sofic (`kun-thom-clifford-cover-weakly-sofic`), and
  `F_3[E_S] = F_3[W] x A_S` (`clifford-cover-group-algebra-splits-into-wreath-and-skew-ring`). So a one-sided
  inverse in `A_S` (`clifford-cover-anti-half-skew-ring-not-directly-finite`) refutes this claim, which is why that
  claim is listed under `refuted_by`.
- **Where it stops.** There is no argument from a length to a rank, and no weakly sofic, non-linear-sofic group is
  known.
