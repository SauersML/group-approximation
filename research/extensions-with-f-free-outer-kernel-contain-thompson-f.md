---
rg: 2
id: extensions-with-f-free-outer-kernel-contain-thompson-f
kind: claim
title: If G/K contains Thompson's group F and Out(K) contains no copy of F, then G contains F
distinct_from:
  central-extensions-of-thompson-f-contain-f: that is the case of an abelian central kernel; this allows any kernel whose outer automorphism group has no copy of F, and reduces to that case through the centralizer of the kernel.
  oligomorphic-fp-infinity-actor-without-thompson-f: that is FFKLZ Question 2.4; this shows that a non-faithful action cannot hide F in the kernel, unless the kernel's outer automorphism group contains F.
---

**ESTABLISHED** through `extensions-with-f-free-outer-kernel-contain-thompson-f-proof` (lane
bh-free-24, 2026-09-18; elementary, not reviewed). No novelty is claimed.

**Statement.** Let `1 → K → G → Q → 1` be a group extension. Suppose `Q` contains a subgroup
isomorphic to Thompson's group `F`, and `Out(K)` contains none. Then `G` contains a subgroup
isomorphic to `F`.

**When the hypothesis on `Out(K)` holds.** `Out(K)` contains no `F` whenever it is residually
finite, since a residually finite group has no infinite simple subgroup such as `F'`, and `F'`
contains copies of `F`. It is also enough that `Out(K)` be linear, or lie in Kropholler's
class `HF`. This covers:
- finite `K`;
- finitely generated abelian `K`, where `Out = GL_n(Z) ⋉ finite`;
- `K` with finite `Out(K)`;
- free groups, surface groups and RAAGs, whose `Out` is residually finite (standard, not
  re-read).

**Consequence for FFKLZ Question 2.4.** Let `G` act on `S` with kernel `K`, and suppose
`Out(K)` contains no `F`. If `G` contains no `F`, then `G/K` contains no `F`. So passing to a
non-faithful action gains nothing: `G/K` is an `F`-free group acting faithfully and
oligomorphically on `S`. The only exception is a kernel whose outer automorphism group
contains `F`.
