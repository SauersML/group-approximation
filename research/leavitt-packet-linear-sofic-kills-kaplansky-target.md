---
rg: 2
id: leavitt-packet-linear-sofic-kills-kaplansky-target
kind: claim
title: The OpenAI nine-leaf packet is the whole Leavitt unit group, so its F_2-linear soficity would make F_2[L^x] stably finite
distinct_from:
  linear-sofic-group-algebra-is-stably-finite: that is the finiteness consequence of linear soficity for an arbitrary group and field; this applies it to the one group L^x and identifies the nine-leaf packet with all of L^x, so the packet question is not a local question about balls or supports.
  openai-nine-leaf-leavitt-configuration: that asserts the criterion hypotheses of the packet and records G = R^x in passing; this draws the Kaplansky consequence of F_2-linear soficity of that G and calibrates the hinge question.
  leavitt-unit-group-algebra-not-directly-finite: that is the open direct-finiteness target; this says F_2-linear soficity of the packet refutes it, and conversely that any witness refutes F_2-linear soficity of the packet.
---

**ESTABLISHED.** Let `R = L_(F_2)(1,2)`, and let `Gamma = EL_alpha(R)`, `u`,
`v` be the nine-leaf configuration of
[[openai-nine-leaf-leavitt-configuration]]. Then

```text
<Gamma, u, v>  =  EL_D(R)  =  R^x .
```

## Consequences

- **The positive side.** If the packet `EL_D(R)` is `F_2`-linear sofic, then
  `K[R^x]` is stably finite for every field `K` of characteristic two, and
  [[leavitt-unit-group-algebra-not-directly-finite]] is false.
- **The negative side.** If `alpha beta = 1 != beta alpha` for some `alpha`,
  `beta` in `K[R^x]` with `char K = 2`, then the packet is not `F_2`-linear
  sofic.

## Calibration of the hinge

- "Is the packet `F_2`-linear sofic?" is exactly "Is `L^x` `F_2`-linear
  sofic?". It is a statement about the whole unit group, so no search family
  inside `L^x` evades it: `EL_D` balls, Thompson `V` balls and transporter
  families all sit in the same group.
- A positive answer kills every direct-finiteness witness over every field of
  characteristic two at once, not just the witnesses supported in the packet.
- The hinge is open. Its defect form is
  [[f2-linear-sofic-groups-kill-rigid-compression-defects]]: if `F_2`-linear
  sofic groups kill rigid defects, `L^x` is not `F_2`-linear sofic, because
  it carries a nontrivial defect. That outcome blocks the stable-finiteness
  argument but produces no one-sided inverse.

Proof: [[leavitt-packet-linear-sofic-kaplansky-proof]].
