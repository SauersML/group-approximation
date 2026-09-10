---
rg: 2
id: fpbs-burnside-upper-cost-one
kind: claim
title: All sufficiently large odd Burnside groups have upper cost one
root: true
---

OPEN. Prove c_n=1 throughout the stated exponent range. The common-upper-cost result would then give fixed price one to every infinite subgroup in these families. This restricted assertion would not settle universal Fixed Price or universal Benjamini-Schramm.

## Attempts

* **Optimize the explicit one-stage certificate.** Response 34
  (`research/artifacts/fpbs/docs/fixed-price-burnside-explicit-bound.md`)
  proves the every-action bound `C <= U_n` for `B(2,n)` and its infinite
  subgroups (`fpbs-qb-action-bound`), improving the elementary `2-2/n` by
  charging selected and repaired domains once and pruning a redundant edge
  from every fully retained finite generator cycle;
  `fpbs-prime-divisor-upper-cost` and `fpbs-priority-burnside-product` sharpen
  it further. **Where it dies:** Section 6 proves `n(2-U_n)/log n -> 1` and
  `2-U_n <= 2/n + log(n)/(n-1)` uniformly, so `U_n` tends to two, not one, and
  optimizing this certificate cannot approach one. Section 7 adds that the
  construction does not self-improve: after thinning and repairing the
  `a`-edges there is no proved second family of independent certificates with
  the same advantage, so reapplying it returns the same bound instead of
  multiplying the excess by a factor below one.
* **Average torsion connector defects.**
  `fpbs-average-connector-defect-cost-bound` bounds relative generator repair
  by the average torsion-weighted connector defect, and
  `fpbs-burnside-low-cost-averaged-connector-target` is the object it needs.
  **Where it dies:** that target is unconstructed, and the hyperfinite
  implementations are barred by `fpbs-cap-hyperfinite-barrier` and
  `fpbs-cap-robust-barrier`, which kill
  `fpbs-dead-hyperfinite-small-average-defect` and
  `fpbs-dead-hyperfinite-plus-null-exception`.
* **Adaptive overlap or fractional cuts.** `fpbs-cap-completion-criterion` and
  `fpbs-cut-completion-criterion` are two different sufficient criteria whose
  hypotheses evade the hyperfinite barrier. **Where it dies:** both wait on
  unconstructed objects, `fpbs-cap-construction-target` and
  `fpbs-cut-burnside-network-target`.
* **Select a phase of the finite skew product.** **Dead:**
  `fpbs-dead-phase-selection-cheap-repair`. By
  `fpbs-finite-phase-section-normalization` a single measurable phase carries
  exactly the kernel-action cost, so selecting one phase restores the cost
  that finite-sheet normalization suppressed; the phase kernels have cost
  `c_n` and supply nothing unless `c_n` was already one.
* **Read it off the literature.** Donoso-Echenique and Silva prove infimal
  group cost one for sufficiently large odd free Burnside groups. **Where it
  dies:** their article explicitly distinguishes that from fixed price one,
  and Bernoulli cost one is what Abert--Weiss would need in order to transfer
  the value to every free action.
