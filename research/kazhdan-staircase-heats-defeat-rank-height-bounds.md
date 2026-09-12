---
rg: 2
id: kazhdan-staircase-heats-defeat-rank-height-bounds
kind: claim
title: Canonical heat for one fixed Kazhdan group realizes staircase asymmetry with bounded rank at each fixed tolerance
artifacts:
  - research/artifacts/kazhdan-staircase-heat-and-central-height-2026-09-08.md
---

There are exact representations `pi_n:SL_3(Z)->U(d_n)` whose
normalized characters converge to the regular character, and unitaries
`U_n`, with the following properties. Write `A_n=pi_n(SL_3(Z))'`,
`B_n=U_n A_n U_n*`, and let `E_n,F_n` be their expectations. Then

```text
||F_n E_n-E_n||_(infinity->2)=1/sqrt(n),
||E_n F_n-F_n||_(infinity->2)=sqrt(1-1/n).
```

The second norm is attained on an explicit unitary. The same fixed
twelve elementary generators have lazy adjoint averages `T_n` with
a gap `gamma>0` independent of `n`. Their actual heat maps satisfy

```text
||exp(-t(I-T_n))-E_n||_(2->2)<=exp(-gamma t).
```

For every fixed `0<eta<1`, all these sufficiently long-time heats have
self-adjoint bistochastic UCP approximations of Kraus rank at most
`13^ceil(log(2/eta)/(-log(1-gamma)))`, independently of `n`.

Nevertheless, the physical versus regular central trace distortion
of `A_n` diverges. Every central corner with distortion bounded by a
fixed constant has physical trace tending to zero. There are also
self-adjoint functions `z_n` of the central log weights with

```text
tr(z_n)=0,       ||z_n||_op=1/2,
||z_n||_2^2=(n+1)/(12(n-1)),
||[U_n,z_n]||_2^2=1/(n-1).
```

Thus canonical Kazhdan heat, one-sided expectation asymmetry,
unbounded central distortion, and nonzero almost-invariant central
heights do not force growing Kraus rank at a fixed positive
approximation tolerance. This does not provide the joint native
Leavitt relations involving its subgroup, compressor and complement.
It does not refute heat rounding: these heats round to `E_n`.

DERIVATION
tail-tensor-representations-realize-kazhdan-staircases
