---
rg: 2
id: ternary-weakly-finite-representations-kill-two-root-defect
kind: claim
title: Every homomorphism from the ternary Leavitt unit group into the units of a weakly finite F_3-algebra kills the two-root defect
distinct_from:
  ternary-leavitt-units-have-no-weakly-finite-representation: that is triviality of every weakly finite representation; this is vanishing of the single element D = N_23 N_12 in each, equivalent by weakly-finite-leavitt-representations-killing-defect-are-trivial, and it is the form a gate proof has to reach.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the rank-function form, weaker in general; this is the weakly finite form, which refutes Gottschalk outright.
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x = EL_3(R)` in the three-leaf frame, and `rho : G -> W^x` a homomorphism into
the units of a weakly finite `F_3`-algebra. Then `(rho(x_23(1)) - 1)(rho(x_12(1)) - 1) = 0`.

**Why it is the counterexample.** With `weakly-finite-leavitt-representations-killing-defect-are-trivial` it
gives `ternary-leavitt-units-have-no-weakly-finite-representation` (route
`no-weakly-finite-representation-from-defect-killing`). That statement is equivalent to
`ternary-anti-central-summand-has-no-weakly-finite-image` and refutes Gottschalk on `G`.

**The tools a proof may use.** In any such `W`, one-sided inverses are two-sided, exact relations of `G`
hold, and `rho(z)` may be taken to be `-1` (artifact Theorem 3). Rank inequalities are unavailable.

## Attempts

- 2026-09-12 `w5-wf-obstruct`: stated as the gate in weakly finite form (artifact Section 2, Corollary 3.2).
  - **Scales.** A nontrivial weakly finite representation has a nonzero defect in every nested corner cut
    along `iota` (Corollary 3.4).
  - **Firewalls.** The landed rank-model firewalls apply verbatim, since their models live in weakly finite
    algebras.
  - **No proof found.**
