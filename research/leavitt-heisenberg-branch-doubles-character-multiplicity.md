---
rg: 2
id: leavitt-heisenberg-branch-doubles-character-multiplicity
kind: claim
title: One Morita branch doubles central-character multiplicity on the marked Leavitt sector
distinct_from:
  compression-defect-dies-in-finite-dimensions: that is the general sterility theorem for the intrinsic defect of an arbitrary pair L <= H, proved by showing compressors normalize the commutant; this is a mechanism special to the marked Leavitt sector which reaches the finite-dimensional conclusion through central-character multiplicity alone, with no commutant, no property (T) and no Kazhdan constant anywhere in the argument.
  oriented-schur-child-branching-identity: that doubles the total branch multiplicity of a Schur child carrying a BCS predicate; this doubles the multiplicity of a single central character under one Morita branch of the binary Leavitt ring composed with a transverse Steinberg shear, and the doubling is per-character rather than aggregate.
  bare-self-copy-mf-calibration: that calibrates the gap between exact finite-dimensional sterility and MF sterility on a torsion-free one-relator group; this is the finite-dimensional half itself for the marked Leavitt defect, and says nothing about microstates.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
  - non_mf_groups_exist.tex
  - GroupApproximation/Criterion/CompressionCentralizerDefect.lean
---

**ESTABLISHED, PROPERTY-(T)-FREE.**  Work on a marked central-character
sector of the binary Leavitt ring `R = L_(F_2)(1,2)`.  The Morita branch

```text
X(a) |-> X(a t_0)
```

together with the transverse shear `Y(s_1)` acts on `X(R)`-characters by a
*nonzero translation lying in the kernel of the branch pullback*.  Write `F`
for the resulting operation on characters.

Because the translation is nonzero and lies in that kernel, every character
`chi` occurring with multiplicity `m(chi)` acquires a distinct companion of
the same multiplicity inside the same branch fiber.  Branch conjugacy then
gives

```text
m(F chi) >= 2 m(chi).                                   (MD)
```

Taking a character of maximal multiplicity contradicts finite
dimensionality.  Hence the marked Leavitt defect dies in **every exact
finite-dimensional representation**.

## Why this is worth a separate node

The conclusion is not new -- `compression-defect-dies-in-finite-dimensions`
already gives finite-dimensional sterility for every compression-centralizer
defect.  What is new is the *mechanism*: `(MD)` uses only orthogonal
self-copy and the Heisenberg commutator law.  It never forms the commutant of
the image, never invokes property (T), and never mentions a Kazhdan constant
or a spectral gap.  That matters because the commutant route is exactly the
step that fails to survive passage to approximate models, so a mechanism that
avoids it is the natural candidate to lift.

Whether it *does* lift is settled negatively by
`leavitt-character-mass-escapes-to-finer-characters`, which is why this node
is filed as finite-dimensional only.

## Attempts

- Passing `(MD)` directly to matrix microstates fails; the failure mode is
  isolated in `leavitt-character-mass-escapes-to-finer-characters`.
- Strengthening `(MD)` to a uniform multiplicity bound independent of the
  representation does not help on its own: the bound one gets is per-fiber,
  and the fibers refine as the dimension grows.
