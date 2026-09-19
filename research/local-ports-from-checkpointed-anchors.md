---
rg: 2
id: local-ports-from-checkpointed-anchors
kind: route
title: A constant-rate backward recursion with constant-spacing anchors is a local port bound
target: local-syndrome-port-domination-at-each-gadget
requires: [backward-syndrome-recursion-holds-for-the-amplifier, bounded-horizon-syndrome-anchor-exists, checkpointed-syndrome-recursion-kills-depth-loss]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

## Why sufficient

`backward-syndrome-recursion-holds-for-the-amplifier` supplies (BSA1) with a
depth-independent `L`, and `bounded-horizon-syndrome-anchor-exists` supplies
checkpoints at spacing at most `r = O(1)` satisfying `b_c <= A e_c` with
`A = O(1)`.  Apply `checkpointed-syndrome-recursion-kills-depth-loss`: for
every layer `t`, with `c` the next checkpoint,

```text
b_t <= L^r ( sum_(s=t)^(c-1) e_s + A e_c ).
```

Read the right side as a local charge.  Put `C_0 = L^r max(1,A)` and
`N(t) = {t, t+1, ..., c}`, an interval of width at most `r+1`.  Then

```text
b_t <= C_0 sum_(s in N(t)) e_s,
```

with `C_0` depending only on `L`, `r`, `A` -- constants, by hypothesis, in
the depth, the qudit count and the state.  Because (BSA1) is asserted in
every state, so is this, and a family of inequalities `Tr(B_t rho') <= C_0 Tr(sum_(N(t)) h'_a rho)`
valid in every state is the operator inequality (LSP1).  The neighbourhoods
are intervals of width at most `r+1` indexed by their left endpoint, so each
layer lies in at most `r+1` of them and the occurrence bound is `R = r+1`.

## What it does not supply

Commutativity, terminality and locality of the ports themselves are carried
by `backward-syndrome-recursion-holds-for-the-amplifier`, which quantifies
over the ports of `local-syndrome-port-domination-at-each-gadget`; this route
supplies only the domination constant.  Both prerequisites are open, and
`bounded-horizon-syndrome-anchor-exists` is the one where the design
difficulty sits: it must separate the logical algebra from the syndrome
register at bounded horizon without measuring the witness.
