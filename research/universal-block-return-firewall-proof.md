---
rg: 2
id: universal-block-return-firewall-proof
kind: route
title: Evaluate the proposed block return in the left regular finite factor
target: universal-block-return-violates-the-regular-firewall
requires:
  - trace-cyclic-rank-mismatch-checksum
---

Extend the canonical trace of `L(Gamma)` to matrices by the normalized
matrix trace.  It is finite and cyclic.  At zero presentation defect,
`(UBR2)` gives

```text
tau(YX)=tau(E),        tau(XY)=tau(E-H).                (UBP1)
```

Cyclicity makes the two left sides equal, so `tau(H)=0`.  Since `H` is a
positive projection and the trace is faithful, `H=0` in
`M_n(L(Gamma))`.  The left regular representation is faithful on the group
algebra, contradicting the hypothesis `H!=0`.

Common spectator amplification changes neither conclusion: normalized
traces factor over the spectator identity.  The same argument applies to
any proof of `(UBR2)` made only from tracial `L2` inequalities and exact
finite-packet conditional expectations, since each such operation exists
unchanged in `L(Gamma)`.

