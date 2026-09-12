---
rg: 2
id: omega-input-reduces-to-mikaelian-tower-proof
kind: route
title: Name the tower, split benignness from the normal form, and read the notation right
target: omega-input-reduces-to-mikaelian-tower
requires: []
artifacts:
  - GroupApproximation/Higman/OmegaTower.lean
  - GroupApproximation/Higman/OmegaTowerStages.lean
---

Machine-checked as a reduction: `omegaInput_of` takes `OmegaTowerInput` and
returns `OmegaInput`, and `zeta_pi_omega_closures_of_tower` carries it into the
three closures that consume it.

**The shape.**  `benignTF_ASub_omegaOp_of_tower` is the step that matters: from
a tower `T` and a `TowerClosure T B`, benignness of `A_(omega_m B)` follows.
The `benign` field supplies a benign witness upstairs and the `descent` field
is what pulls membership back down to the operation's subgroup; neither is
about the operation, which is the point of the repackaging.

**Why the stages are HNN extensions.**  Reading `*_P` as §2.4's multiple HNN
extension --- new generators centralizing a common subgroup --- puts every
stage inside `Higman.CentHNN`.  Had it been read as an amalgamated product, the
lane would have needed pushout normal forms, which is a materially larger
obligation and one the repository only acquired later on a different lane.

**Why the shift and not the reversal.**  `Omega = Pi *_rho r` conjugates `F_3`
by `shiftAut^m`.  The reversal reading gives a group in which the coded
sequences are not shifted at all, so the block condition cannot be expressed;
the tower would be well defined and useless.

## The boundary

`OmegaTowerInput` is not proved.  What is proved is that it suffices, and that
the object it quantifies over is the correct one --- which is exactly what the
three corrections buy.  Anyone attempting it should read
[[mikaelian-rho-tau-shortcuts-fail]] first, because the same section of the
same paper is unreliable two clauses away.
