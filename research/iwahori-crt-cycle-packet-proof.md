---
rg: 2
id: iwahori-crt-cycle-packet-proof
kind: route
title: Tensor the five presentation words and count diagonal cycles by CRT
target: iwahori-cycle-packets-are-crt-tensor-closed
requires:
  - iwahori-weil-cycle-packets-extend-exactly
---

Each defining relation is a word equal to the identity, so evaluating it on
the tensor tuple `(X_1 tensor X_2,R_1 tensor R_2,S_1 tensor S_2)` gives the
tensor product of two identities.  Coprimality of `q_1,q_2` identifies the
product eigenvalue characters with the CRT character group of order
`q_1q_2`.  On two cycles of lengths `m_1,m_2`, diagonal translation has
orbit length `lcm(m_1,m_2)` and therefore has
`m_1m_2/lcm(m_1,m_2)=gcd(m_1,m_2)` orbits.  This proves the exact closure and
the packet count.
