---
rg: 2
id: fpbs-burnside-positive-upper-cost
kind: claim
title: Some sufficiently large odd Burnside exponent has upper cost strictly greater than one
root: true
distinct_from:
  fpbs-burnside-upper-cost-one: that asserts upper cost one for all sufficiently large odd exponents; this asserts upper cost above one for some exponent. They are mutually exclusive rather than duplicates, and neither is established.
---

OPEN. Prove c_n>1 for some exponent in the scope of the algebraic inputs. Together with fpbs-burnside-explicit-action-pair this would give a Fixed Price counterexample. No strict lower bound beyond one is established here.

## Attempts

* **Turn the spectral phase-disagreement bound into a cost lower bound.**
  Section 7 of `research/artifacts/fpbs/phase-repair.md` proves that any
  balanced `Z/qZ` phase labeling of a Bernoulli action of a nonamenable group
  has average generator disagreement at least `(1-rho)(1-1/q)`, a genuine
  positive lower bound. **Dead:** `fpbs-dead-phase-disagreement-positive-cost`,
  invalidated by `fpbs-finite-phase-disagreement-versus-repair`. For `q=2` and
  the standard four-generator set of `F_2` the disagreement bound is
  `(1-sqrt(3)/2)/2` while the optimized relative repair cost is exactly zero.
  A sum of direct generator-disagreement measures bounds one particular repair
  scheme from above; cost theory permits long shared rerouting, so it is not a
  lower bound on optimized graphing cost.
* **Use the hyperfinite barrier as a lower bound.**
  `fpbs-cap-hyperfinite-barrier` gives a uniform positive floor
  `epsilon_n=(1-rho_n)/L_n` on mean connector defects for hyperfinite
  subrelations, and `fpbs-cap-robust-barrier` shows it survives deletion of a
  small exceptional set. **Where it dies:** Section 5 of
  `research/artifacts/fpbs/connector-capacity.md` states that this is not a
  cost statement, and that low cost does not imply hyperfiniteness.
  `fpbs-cut-low-cost-seeds` exhibits ergodic, nowhere-hyperfinite subrelations
  of cost `1+t` for every `t>0`, so the barrier is silent about them.
* **Get a lower bound from L2-Betti numbers.** `fpbs-amen2-betti-cost-input`
  gives `beta_1^(2)(Gamma) <= C(alpha)-1`. **Where it dies:** no positive
  value of `beta_1^(2)` is available for these groups in the archive, and the
  inequality is uniform in the action, so even a positive value would raise
  both costs of `fpbs-burnside-explicit-action-pair` together.
* **Direction of the whole programme.** Every constructed route in the archive
  pushes `c_n` down, not up: `fpbs-qb-action-bound` with `U_n -> 2`,
  `fpbs-prime-divisor-upper-cost`, and the three cost-one targets
  `fpbs-burnside-low-cost-averaged-connector-target`,
  `fpbs-cap-construction-target`, `fpbs-cut-burnside-network-target`. No lower
  bound above the universal value one is established anywhere, which is why
  `fpbs-burnside-explicit-action-pair` records two costs without asserting
  that they differ.
