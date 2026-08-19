---
rg: 2
id: a4-regular-three-way-coherence-transducer
kind: claim
title: The regular A4 three-dimensional block is a lossless three-way coherence transducer
---

In a multiple of the regular `A4` representation, let `P_chi` be the three
`C3` character projections, `E_chi` the three line carriers, and put

```text
R_chi = P_chi-E_chi,
E = sum_chi E_chi,
S = Q_+-E,
```

where `Q_+=(1+rho(b))/2`.  Then every `R_chi` and `S` has normalized trace
`1/4`.  The operators

```text
T_chi = sqrt(3) S R_chi
```

are partial unitaries with

```text
T_chi^* T_chi = R_chi,
T_chi T_chi^* = S.                                     (A4-FAN)
```

Consequently the off-diagonal `C3` blocks of the involution `b` are lossless:
for `chi != psi`,

```text
(3/2) R_chi rho(b) R_psi = T_chi^* T_psi
```

is a unitary identification from `R_psi` onto `R_chi`, while the diagonal
blocks are fixed scalars

```text
R_chi rho(b) R_chi = -(1/3) R_chi.                     (A4-DIAG)
```

Thus the scalar `C3`-to-`C2` overlap channel is maximally uninformative, but the
same regular A4 context retains a **lossless matrix-valued three-way phase
channel** on a trace-`3/4` sector.  The external multiplicity appears only as a
common tensor multiplicity of these partial-unitary coherence blocks.

This is a finite compiler interface for the atlas agreement problem: a context
should be propagated through the normalized exact network using the
`T_chi^*T_psi` coherence blocks, not through the rank-one scalar character
overlap matrix.