---
rg: 2
id: iwahori-cycle-packets-are-crt-tensor-closed
kind: claim
title: Exact Iwahori cycle packets are closed under coprime CRT tensor products
artifacts:
  - experiments/bs14_cycle_packet_probe.py
  - experiments/bs14-cycle-packet-probe-smoke.json
distinct_from:
  iwahori-weil-cycle-packets-extend-exactly: that supplies the prime Weil packets; this combines any two exact packets and computes the orbit splitting of the tensor product.
  bs14-relative-involution-extension-stability: that is a uniform approximate repair theorem; this is an exact closure operation and does not control near-solutions.
---

Suppose exact packets `(X_i,R_i,S_i)` satisfy the corrected five-relator
Iwahori presentation, with `S_i` of coprime odd orders `q_i` and with one
fourth-power spectral orbit of length

```text
m_i=ord_(q_i)(4),       i=1,2.                         (CTP1)
```

Then

```text
X=X_1 tensor X_2,
R=R_1 tensor R_2,
S=S_1 tensor S_2                                      (CTP2)
```

is again an exact Iwahori extension.  Indeed every defining word evaluates
tensorwise, so the involution, `BS(1,4)`, and both cubic relations remain
exact.

Under the Chinese remainder identification of roots of orders `q_1,q_2`
with roots of order `q_1 q_2`, the joint `S`-spectrum is the Cartesian
product of the two cyclic fourth-power orbits.  Diagonal fourth-power
translation has

```text
gcd(m_1,m_2) orbits, each of length lcm(m_1,m_2).      (CTP3)
```

Thus the tensor product is a direct sum of `gcd(m_1,m_2)` exact cycle
packets.  In particular, if `m_1,m_2` are coprime it is one
multiplicity-one packet for modulus `q_1q_2`.

Combining the one-dimensional modulus-`3` packet with the prime Weil packets
gives the exact composite packets at `q=21,33,57,69`; combining the
coprime-length prime packets at `7` and `11` gives the exact packet at
`q=77`.  The bounded phase probe recovers all five with residuals around
`10^(-10)` or smaller, independently confirming the word conventions.

This closure explains a nontrivial part of the exact solution locus that a
relative stability proof must preserve: arithmetic packets occur in CRT
families and can split into repeated equal orbit packets when the orbit
lengths share a divisor.
