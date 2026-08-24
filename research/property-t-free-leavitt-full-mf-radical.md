---
rg: 2
id: property-t-free-leavitt-full-mf-radical
kind: claim
title: Derive binary-Leavitt full MF collapse without Kazhdan hypotheses
root: true
goal: true
artifacts:
  - research/property-t-free-leavitt-via-corona-module-decoder.md
  - research/property-t-free-leavitt-via-full-support-hs-decoder.md
  - research/property-t-free-leavitt-via-opnorm-return-row.md
  - research/property-t-free-leavitt-via-atomic-morita-return.md
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

OPEN.  Let `R=L_(F_2)(1,2)` and let

```text
Delta=St_20(R),                    z=x_13(s_1t_1).
```

The root `z` is a nontrivial involution and normally generates `Delta`.
Prove

```text
Rad_MF(Delta)=Delta
```

without assuming property `(T)` for either a compression source or the
ambient group.  More general elementary-group versions are welcome, but the
literal binary-Leavitt Steinberg group is the fixed target of this goal.

The proposed route is intrinsic to norm matrix coronas.  A surviving root
has exact finite additive and Heisenberg multiplicity germs.  The remaining
step is to assemble those germs into one nonzero finitely generated
projective corona module carrying a unital action of `R`.  Rank-germ
Hilbert-hotel cancellation would then force that module to vanish.

There are now four sharply separated routes.

1. Assemble finite root germs into one finite-projective norm-corona
   coefficient module and apply rank-germ Hilbert-hotel cancellation.
2. Reblock to a positive-density active core, construct the corresponding
   normalized-Hilbert--Schmidt coefficient module, and apply tracial
   cancellation.
3. Recover exact depth-one and depth-two packets on one nonzero carrier and
   authenticate one operator-norm coarse-to-fine return row.
4. Return only the two diagonal inverse rows and completeness row of one
   binary Leavitt cell to the prescribed nontrivial `z`-spectral atom and
   apply the Atomic Leavitt Gap.

The fourth route proves that positive carrier density, global module gluing,
off-diagonal Leavitt rows and exact `M_2/M_4` packet ranks are unnecessary at
the terminal MF step.  Its unresolved content is still a genuine
finite-matrix same-atom decoder: the algebraic root presentation does not by
itself identify the returned coefficient arrows with that prescribed
spectral projection.
