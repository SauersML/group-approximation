---
rg: 2
id: bounded-horizon-syndrome-anchor-exists
kind: claim
title: Every constant number of layers carries a syndrome anchor charged by its own local energy
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

Hypothesis (CKP) of `checkpointed-syndrome-recursion-kills-depth-loss`,
realized.  There is `r = O(1)` such that every interval of `r` layers of the
amplified instance contains a checkpoint `c` whose bad syndrome weight is
charged by the parent-Hamiltonian energy at `c` alone:

```text
b_c <= A e_c,          A = O(1) independent of the code size.   (ANC1)
```

The anchor must **separate** the logical algebra from the syndrome register
without measuring the arbitrary logical witness, and must be produced and
tested inside a bounded horizon: if the gadget realizing (ANC1) needs a
decoder whose depth grows with the global code, then
`checkpointed-syndrome-recursion-kills-depth-loss` merely replaces circuit
depth by decoder depth and the loss vanishes asymptotically again.

## Attempts

- **Knill--Laflamme as the anchor.**  It supplies the separation abstractly:
  on a correctable error family, `P E_alpha^* E_beta P = c_(alpha beta) P`
  and coherent recovery `R E_alpha P = P tensor |s_alpha>` make the syndrome
  register testable while the logical state stays arbitrary.  What is missing
  is quantitative and is exactly (ANC1): a constant-locality parent-Hamiltonian
  inequality charging the syndrome weight to the local energy, with `A`
  independent of code size.  Because that gap is a whole hypothesis and not a
  step, no route from Knill--Laflamme into this claim is written.
- **Use the ABN terminal boundary as the only anchor.**  That is the
  unanchored case: one checkpoint at distance `D` gives `r = D` and the
  factor `L^D` recorded in
  `abn-energy-to-fault-loss-is-exponential-in-depth`.
- **Anchor at every layer.**  Would give `r = 1`, but an anchor per layer is
  a measurement per layer, and the design constraint is that anchors
  synchronize *fault frames*, not the logical state; per-layer logical
  measurement is excluded by no-cloning and local indistinguishability.  The
  open question is whether fault-frame anchors alone can be placed at
  constant spacing.
