---
rg: 2
id: leavitt-d4-l14-rank9-six-classes-proof
kind: route
title: Rank and cyclically classify the first length-fourteen profile
target: leavitt-d4-l14-profile-has-six-rank9-cyclic-classes
requires:
  - leavitt-d4-length12-balanced-rank9-is-fenced
---

The generalized ranker was run through the MSI wrapper as job `16675107`
with one CPU and 1 GiB of memory.  For the completed profile
`---+-+-+++++++` it returned

```text
rank 9: 18, rank 10: 390, rank 11: 2223,
rank 12: 2619, rank 13: 420.
```

All systems are carrier-balanced.  Quotienting cyclic rotations exactly as
in the length-twelve classifier gives six classes, each represented three
times:

```text
normal:  0;115  2;115  0;412
inverse: 0;142  1;115  3;115.
```

Here `start;sizes` records the first atom and the three cyclic contiguous arc
sizes on the seven-valent face.  Global inversion is deliberately not used:
on a stored fixed sign representative it also requires the ambient slot
reversal/rotation.

For the normal `1;151` representative (cyclic key `0;115`), write the two
trivalent factors as `(H Ai,H^-1 Bi,H^-1 Ci)` and the seven-valent atoms as

```text
T0=H E1, T1=H^-1 E2, T2=H E3, T3=H^-1 E4,
T4=H E5, T5=H^-1 E6, T6=H^-1 E7.
```

The exact carrier equations and boundary are

```text
H A0=E1^-1 H^-1,
H^-1 C0=A1^-1 H^-1,
H^-1 C1=E2^-1 H,
K=H^-1B0 H^-1B1 H E3 H^-1E4 H E5 H^-1E6 H^-1E7.
```

Unlike length twelve, `A1` is a seven-syllable alternating word in copies 3
and 2, so its noncrossing cancellation branches are genuinely new.

