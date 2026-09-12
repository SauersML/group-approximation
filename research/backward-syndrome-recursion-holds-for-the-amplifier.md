---
rg: 2
id: backward-syndrome-recursion-holds-for-the-amplifier
kind: claim
title: The amplified instance satisfies a constant-rate backward syndrome recursion
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

Hypothesis (BSR) of `checkpointed-syndrome-recursion-kills-depth-loss`,
realized for the output of
`locality-preserving-constant-combinatorial-gap`.  There are commuting local
syndrome ports whose expected weights `b_t = Tr(B_t W rho W^*)` at layer `t`,
and the parent-Hamiltonian energies `e_t = sum_(a at layer t) Tr(h'_a rho)`,
satisfy

```text
b_t <= L ( e_t + b_(t+1) )   in every state rho,   L = O(1).    (BSA1)
```

`L` must not depend on the depth, on the number of qudits, or on the state.
The estimate is one backward step of the Anshu--Breuckmann--Nguyen light-cone
argument, stated for the amplified construction and for the ports of
`local-syndrome-port-domination-at-each-gadget` rather than for a
particular Bell-basis bookkeeping.

## Attempts

- **Quote ABN directly.**  Their argument is run to a terminal boundary and
  its published conclusion is the depth-vanishing threshold recorded in
  `abn-energy-to-fault-loss-is-exponential-in-depth`, so what can be quoted is
  the *iterated* statement, not the one-step constant `L`.  Extracting a
  one-step constant is a re-derivation against their construction, not a
  citation, and it must be redone for the amplified instance in any case.
- **Take (BSA1) as a definition of the ports.**  Circular: the ports also
  have to satisfy (LSP1) and be terminal and local, and a family defined to
  satisfy the recursion carries no reason to satisfy those.
