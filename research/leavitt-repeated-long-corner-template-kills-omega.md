---
rg: 2
id: leavitt-repeated-long-corner-template-kills-omega
kind: claim
title: Repeating both trivalent tails transports the source commutator to the target
artifacts:
  - research/leavitt-repeated-long-corner-template-proof.md
distinct_from:
  leavitt-direct-tail-transport-screen-is-empty: that asks two separate trivalent tails to equal unary corners in the earlier short packet layouts; this isolates the exact shared-tail Tietze mechanism and permits compound coefficient slots.
---

In the degree-four sign topology `++-++-++`, put the source gates `a,b` and
target gates `c,d` in the four sign-change slots.  If the unary long corner
`H` and the two trivalent tails `L,N` satisfy

```text
L=H=N
```

inside the coefficient free product, then the four orbit relators force

```text
c=H^(-1)aH,          d=H^(-1)bH.
```

Consequently `[a,b]=1` forces `[c,d]=1`.  For the Leavitt gates recorded in
`leavitt-omega-has-an-explicit-distorted-target`, this kills the nonidentity
mark `[c,d]=x_15(s_0^2)`.
