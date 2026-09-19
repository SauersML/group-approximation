---
rg: 2
id: property-t-free-leavitt-via-thompson-v-not-mf-el
kind: route
title: Reduce the Kazhdan-free St20 goal to the statement that Thompson's V is not MF
target: property-t-free-leavitt-full-mf-radical
requires:
  - thompson-v-not-mf
  - thompson-v-finitely-presented-infinite-simple
  - leavitt-steinberg-map-iso-from-rank-three
  - binary-leavitt-elementary-group-is-simple
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-cylinder-swaps-generate-thompson-in-el
---

Unlike `property-t-free-leavitt-via-el20-comparison`, which moves the goal from
St20 to EL20 and keeps the whole Kazhdan-free difficulty, this route moves the
difficulty into the Haagerup subgroup `V`, where (T) cannot enter at all.

Let `R = L_(F_2)(1,2)`, `Delta = St_20(R)`, `z = x_13(s_1 t_1)`. Here
`Rad_MF(Delta)` is the intersection of the kernels of all homomorphisms
`Delta -> U(Q)` into unitary groups of norm matrix coronas `Q`, as in Step 3 of
`leavitt-st20-t-free-holes-hold-via-kazhdan-proof`.

**Step 1 (Delta is simple).**
- `leavitt-steinberg-map-iso-from-rank-three` (Khanh, Theorem 5.4) gives
  `St_20(R) ~= GL_20(R)`.
- `leavitt-gl-equals-el-and-perfect-unit-group` gives `GL_20(R) = EL_20(R)`.
- `binary-leavitt-elementary-group-is-simple` (internal root detection) makes
  `EL_20(R)` simple.

**Step 2 (V embeds in Delta).**
- The prefix-code self-similarity `R ~= M_20(R)` of
  `leavitt-gl-equals-el-and-perfect-unit-group`, for any complete binary prefix
  code with twenty leaves, gives `GL_20(R) ~= R^x`.
- `leavitt-cylinder-swaps-generate-thompson-in-el` gives `V <= R^x` as the
  cylinder-swap units.
- So there is an injective homomorphism `iota: V -> Delta`.

**Step 3 (kill).** Let `pi: Delta -> U(Q)` be any corona representation.
- `pi o iota` is a corona representation of `V`. By `thompson-v-not-mf` it is
  not injective.
- `V` is simple (`thompson-v-finitely-presented-infinite-simple`), so
  `pi o iota` is trivial and `ker pi` contains `iota(V)`, which is nontrivial.
- `ker pi` is a nontrivial normal subgroup of the simple group `Delta`, so
  `pi` is trivial.

Hence `Rad_MF(Delta) = Delta`. The same three steps give full MF radical for
`EL_n(R)` for every `n >= 3`, for `R^x`, and so the EL20 variant
`property-t-free-el20-full-mf-radical` too.

## Kazhdan hygiene

The prerequisites other than the hole are:
- a Steinberg-group comparison (literature import, no spectral input);
- internal ring identities (`GL = EL`, the prefix-code isomorphism);
- internal root detection for simplicity;
- the cylinder-swap embedding;
- classical simplicity of `V`.

None of them uses property (T), a Kazhdan projection, or
`elementary-group-property-t-over-free-algebras`. The hole cannot be closed
through (T) of an overgroup either: `V` has the Haagerup property, so its
Kazhdan subgroups are finite (`thompson-v-has-no-rigid-compression-defect`).
Also, a corona representation of `V` need not extend to `Delta`. So this route
turns the goal's proof-method restriction into a genuinely mathematical,
non-methodological question. By contrast, w13 found that the goal's other
holes are true through (T) (`leavitt-st20-t-free-holes-hold-via-kazhdan`).

## What the route does not claim

The hole is strictly harder than the goal's equation. That equation is already
a theorem through (T), while `V` MF is open in both directions (see
`classical-unitary-ratio-witnesses-amplify-to-metric-models`, part (C)). If
`V` turns out to be MF, this route dies, and the goal remains open.
`binary-leavitt-mark-is-conjugate-to-thompson-cone-swap` locates the gap: both
the goal and the hole ask whether one cone transposition dies. The goal asks
this in corona representations of `Delta = <V, V^h>`, the hole in those of `V`.
