---
rg: 2
id: ternary-leavitt-units-have-no-weakly-finite-representation
kind: claim
title: The ternary Leavitt unit group has no nontrivial homomorphism into the unit group of any weakly finite F_3-algebra
refuted_by:
  - ternary-leavitt-units-have-a-nontrivial-char-three-rank-model
distinct_from:
  ternary-anti-central-summand-has-no-weakly-finite-image: that is the ring-level statement about quotients of S_-; this is the same content read as a statement about group homomorphisms into units, equivalent by ternary-weakly-finite-representations-give-anti-central-images.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is absence of Sylvester rank functions moving z, weaker in general; this is absence of every weakly finite host algebra, which refutes Gottschalk outright.
artifacts:
  - research/artifacts/weakly-finite-representations-of-ternary-leavitt-units-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`. Every group homomorphism from `G` into the unit group of a weakly finite
`F_3`-algebra (one where `AB = I_n` implies `BA = I_n`) is trivial.

**Status of the equivalences.**
- **Equivalent to** `ternary-anti-central-summand-has-no-weakly-finite-image` (routes
  `no-weakly-finite-representation-from-summand-obstruction` and
  `summand-no-weakly-finite-image-from-no-representation`), and to
  `ternary-weakly-finite-representations-kill-two-root-defect`.
- **Refutes Gottschalk on `G`.** The quotient `F_3[G] -> S_-` has no weakly finite image, so `F_3[G]` is not
  stably finite (artifact Corollary 1.2).

**What refutes it.**
- any overgroup `H` of `G` with `F_3[H]` stably finite;
- any nontrivial characteristic-three rank model of `G`.

## Attempts

- 2026-09-12 `w5-wf-obstruct`: opened as the group form of the target (artifact Section 3).
  - **Stage one.** A certificate must start with an exact one-sided pair over `S_-`. The natural isometry
    lifts are left zero divisors, and their cross term squares to the indicator of a nonempty set of odd
    measures (artifact Section 4).
  - **Firewalls.** Every landed anti-central model (sofic subgroups containing `z`, locally finite bases with
    HNN letters, Fock local letters) lives in a weakly finite algebra. An obstruction must use multi-letter
    relations with overlapping supports, or non-level Steinberg commutators.
  - **E⋊V.** An obstruction using only `E⋊V` would show that `V` has no nontrivial weakly finite
    representation over `F_3`, hence that `V` is not sofic.
  - **No mechanism found.**
