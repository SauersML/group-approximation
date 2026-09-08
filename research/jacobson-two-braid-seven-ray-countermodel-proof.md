---
rg: 2
id: jacobson-two-braid-seven-ray-countermodel-proof
kind: route
title: Realize the full finite packet and both braids in an explicit amenable seven-ray group
target: jacobson-two-braid-infimum-is-zero
requires:
  - jacobson-joint-cells-are-two-braids
  - amenable-implies-operator-mf
  - jacobson-two-braid-gap-characterizes-mark-collapse
  - jacobson-tail-braid-exactification-and-standard-carrier
artifacts:
  - research/artifacts/jacobson-two-braid-seven-ray-countermodel-2026-09-08.md
---

The first prerequisite supplies the exact two-braid presentation. The
artifact constructs a seven-ray action with the natural head representation
on three boundary vectors and the seven-point permutation representation
of the tail at every positive level. Its involution exchanges two head
rays with balanced shifts and swaps two other rays without shifts.

Both braid relations and all overlap relations are checked directly.
The head and tail actions are faithful and have disjoint supports, so the
whole finite packet embeds. The generated group `A_7` has a locally finite
kernel under its eventual translated-ray-permutation map and a virtually
abelian image. It is therefore countable amenable. The second prerequisite
makes `A_7` operator-MF; the third yields `gamma=0`, and the fourth yields
`gamma_tail=0`.

The artifact also verifies that the same quotient satisfies
`[h (I+E_13)_P h,(I+E_23)_P]=1`. Thus this additional literal mixed
commutation still retains the full packet in an amenable quotient.
