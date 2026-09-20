---
rg: 2
id: lcs-fixed-port-ucp-decoders-have-unbounded-trace-cost
kind: claim
title: Fixed-port UCP decoders of the three-control amplifications require diverging trace-density cost
artifacts:
  - research/artifacts/lcs-fixed-port-ucp-trace-cost-2026-09-20.md
distinct_from:
  lcs-auth-three-controls-lose-common-corner-weight: that controls common reducing projections; this allows arbitrary nonreducing unital completely positive maps and measures their state density against normalized input trace, while retaining the specified ports.
---

Use the explicit eight-port group H, representation R_m of dimension
4 times 17^m, and projection b=(1+X)(1-U_0)/4 from
`lcs-auth-three-controls-lose-common-corner-weight`. Let
Phi_m:M_(4 times 17^m)->M_(k_m) be unital completely positive and put
phi_m=tr_(k_m) composed with Phi_m. Suppose

    phi_m(a)<=C_m tr(a) for all positive input matrices a,
    max_s tr(I-Phi_m(R_m(s))^2) -> 0,
    phi_m(R_m(b)) -> 0,

where s ranges over the eight involutory ports. Then C_m tends to
infinity. All traces are normalized.

In particular no bounded-trace-density-cost family of UCP maps sends
these fixed ports to exact unitary ports with a literal controlled-U_0
projection readout. This extends the common reducing-corner obstruction
but does not exclude arbitrary replacement observables or channels
whose trace-density costs diverge.

The artifact proves the finite inequality

    max(0,1-4 phi_m(R_m(b))-8 L_N eta_m)^2
        <= C_m(3/N+9 beta_N^m),

where eta_m is the square root of the maximum port variance,
L_N is the maximum length of N disjoint-support conjugators, and
beta_N<1 comes from their finite word support. No halting reduction
or full quantum hardness theorem follows from this obstruction.
