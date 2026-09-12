---
rg: 2
id: fpbs-burnside-low-cost-averaged-connector-target
kind: claim
title: Construct Bernoulli subrelations of cost tending to one with vanishing average torsion connector errors
root: true
---

**OPEN.** For each large odd exponent, construct the S_m and connector families in Section 8. Theorems 2 and 3 do not supply these objects. Phase sections do not do so unless their common cost was already one. No proving route is provided.

## Attempts

* **Use the phase kernels as the low-cost subrelations.** Section 5 of
  `research/artifacts/fpbs/phase-repair.md` gives the phase kernel `S_c` zero
  relative cost, which looks like a supply of cheap subrelations inside the
  target action. **Where it dies:** Section 8 states that `S_c` does not
  supply the sequence unless `c_n` was already one, because its cost is
  exactly `c_n`; and `fpbs-finite-phase-section-normalization` shows that
  selecting one phase restores the cost that finite-sheet normalization had
  suppressed. The dead route is `fpbs-dead-phase-selection-cheap-repair`.
* **Take the subrelations hyperfinite.** A hyperfinite `S_m` would be the
  easiest source of cost tending to one. **Dead:**
  `fpbs-dead-hyperfinite-small-average-defect`, invalidated by
  `fpbs-cap-hyperfinite-barrier`. In the stated Burnside range every element
  with connection defect below `epsilon_n=(1-rho_n)/L_n` lies in one cyclic
  subgroup of order `n`, so at most `n` terms of any distinct connector list
  can be small and `liminf_k (1/k) sum_i Delta_S(b_i) >= epsilon_n`. The
  averages therefore cannot tend to zero, uniformly over the action, the
  relation and the list.
* **Hide the nonhyperfinite part on a vanishing set.** **Dead:**
  `fpbs-dead-hyperfinite-plus-null-exception`, invalidated by
  `fpbs-cap-robust-barrier`: extending a hyperfinite restriction by singletons
  costs at most `2delta` in each defect, so mean defect tending to zero forces
  every hyperfinite restriction to leave out measure at least
  `epsilon_n/2`.
* **Start from the constructed seeds.** `fpbs-cut-low-cost-seeds` supplies
  actual nested ergodic subrelations `S_t` of cost `1+t` inside the target
  Bernoulli action, nonhyperfinite on every positive-measure restriction, so
  they clear both barriers. **Where it dies:** no connector family is
  exhibited for them. Section 8 of `phase-repair.md` needs disjoint torsion
  detours for every generator with vanishing averaged defects, and neither
  those detours nor the estimate is constructed in the ambient Bernoulli
  action of a large odd-exponent Burnside group.
