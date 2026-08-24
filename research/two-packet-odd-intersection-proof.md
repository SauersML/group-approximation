---
rg: 2
id: two-packet-odd-intersection-proof
kind: route
title: Take the identity coefficient and use self-adjoint packet supports
target: two-packet-solutions-have-odd-intersection
requires:
  - both-rank-three-factors-must-be-packet-corrected
  - two-packet-linear-trace-vanishes
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/verify-kl-gate-c3-corner.py
---

The exact corner normal form gives `tau(Delta)=1`.  Apply `tau` to the packet
equation from the first prerequisite and use the two vanishings from the
second; this leaves `tau(P_xP_y)=1`.

Each packet is self-adjoint, so the identity coefficient of `P_xP_y` is the
parity of `supp(P_x) intersect supp(P_y)`.  If `x=y`, this coefficient is
`tau(P_x^2)=epsilon(P_x)`.  But
`epsilon(P_x)=epsilon(e)^2 epsilon(k)=0`, since `epsilon(e)=0`.  Thus the
intersection is odd and the two conjugators are distinct.
