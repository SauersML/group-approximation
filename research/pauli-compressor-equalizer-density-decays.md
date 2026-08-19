---
rg: 2
id: pauli-compressor-equalizer-density-decays
kind: claim
title: Compressor-fixed Pauli equalizer sectors have zero regular density
artifacts:
  - research/artifacts/pauli-compressor-equalizer-decay-2026-08-18.md
distinct_from:
  exact-joint-compressor-fiber-variance: that no-go keeps a full extension fiber and shows covariance does not classicalize it; this one kills the opposite shortcut, showing that forcing the fresh compressor fibers to be trivial makes the retained regular mass decay by a factor eight per level.
  negative-character-sector-aggregation: that preserves trace one half by summing all negative extension characters; this shows why selecting only characters that identify source and compressed Pauli packets cannot preserve positive density under iteration.
---

Let `alpha(a)=s_0 a t_0` in the binary Leavitt ring and put

```text
q_m=alpha^m(1),
f_j=alpha^j(s_1t_1).
```

For each `j`, the adjacent-root packet

```text
H_j=<x_12(f_j),x_23(f_j)> ~= D_8
```

is a Pauli cell, and the `H_j` commute with one another.  For `m>=1`, the
trivial-character projection of

```text
H_[0,m)=H_0 x ... x H_(m-1) ~= D_8^m
```

has regular trace `8^(-m)`.  On that projection the scalar Pauli triple
`x_12(1),x_23(1),x_13(1)` agrees with the depth-`m` compressed triple
`x_12(q_m),x_23(q_m),x_13(q_m)`.

After also taking the negative cut of `x_13(q_m)`, the equalizer has regular
trace exactly

```text
1/(2*8^m).
```

Compressor covariance shifts `H_j` to `H_(j+1)`.  Hence imposing the equality
conditions on a sector and on its first `r` compressor transports forces
triviality of `H_0,...,H_(m+r-1)` and leaves trace at most

```text
1/(2*8^(m+r)).
```

In particular no compressor-invariant Pauli equalizer sector has positive
regular trace.  A positive-density finite-multiplicity extraction therefore
cannot be obtained by selecting a fixed character fiber on which the source
and compressed Pauli packets agree at every depth.
