---
rg: 2
id: foldable-free-minimal-quantum-rigid-z2-sft-exists
kind: claim
title: Some free minimal quantum rigid Z^2 SFT has a rational determining half-plane (for instance, is corner-deterministic); then F_n x Z carries a free minimal quantum rigid SFT, independently of Labbé's J_2
requires:
  - abht-path-folds-accept-exactly-expansive-rational-half-planes
distinct_from:
  free-minimal-z2-sft-is-quantum-rigid: that asks for a free minimal rigid Z^2 SFT by any mechanism, which the crossing-wire shift claims; this adds the one-sided determinism the ABHT fold needs.
  free-minimal-sft-without-two-sided-faults-exists: that asks for a determining side on every line, with topological freeness, and yields rigidity; this asks for rigidity plus one rational determining side, with freeness.
  jeandel-rao-minimal-subshift-is-quantum-rigid-iff-labbe-shift-is: that makes ABHT's own fibre depend on J_2(Ω_U); this asks for a different fibre, making F_n x Z independent of J_2.
---

**OPEN** (posed by bh-g2-abh, 2026-09-18).

## Statement

There is a `Z^2` SFT `Ω` with four properties:
- it is free;
- it is minimal;
- it is quantum rigid;
- it has a **rational determining normal**: for some `ν ∈ Q^2`, points agreeing on `{⟨z, ν⟩ < t}` are
  equal.

Corner determinism is a sufficient special case: `x(z) = G(x(z+u), x(z+u'))` for one pair of adjacent
unit vectors `u, u'`.

## Payoff

- **`F_n × Z`.** By `abht-path-folds-accept-exactly-expansive-rational-half-planes` (Corollary), every
  `F_n × Z` carries a free, minimal, quantum rigid SFT.
  - Its crossed product over `F_2` is finitely presented and central simple.
  - This is the first free minimal instance of E2 over a one-ended non-amenable group.
  - It does not depend on `J_2(Ω_U)`.
- **Ã2 lattices.** If `Ω` is corner-deterministic in the sense of the cone condition,
  `a2-busemann-transplants-preserve-quantum-rigidity` also gives a free, quantum rigid SFT over the Kazhdan
  CMSZ lattices. Minimality there is `busemann-transplant-minimality-is-horospherical-minimality`.

## Routes and partial results

- **Crossing-wire, variant A4** (bh-g2-fixedpoint-a):
  - `minimal-crossing-wire-fixed-point-shift-is-quantum-rigid` claims free, minimal and rigid, but it is
    not corner-deterministic as landed.
  - Its proof, A4, already allows SW-deterministic macrotiles. The missing piece is SW-determinism of the
    **ground** tile set: wires only up and right, a one-way zone, and SW-fixed skeleton and slots.
- **Horizontally expansive version** (bh-g2-fixedpoint-a, in progress). This is also sufficient, but it
  asks for both sides of one line. Side-local margins plausibly block it: see the assessment in the
  acceptance node.
- **Kari–Papasoglu, Lukkarila.** These give four-way deterministic aperiodic tile sets, recalled and not
  re-read. Minimality and rigidity are unknown: by `four-way-deterministic-sft-rigidity-lives-on-axis-faults`,
  their rigidity is decided on axis faults.
- **No two-sided faults.** A free example for `free-minimal-sft-without-two-sided-faults-exists` would
  settle this node in every rational direction.

## Lesson for general BH

For E2 over non-amenable groups, the `Z^2` crux object should be built corner-deterministic from the start.
Determinism in one corner is exactly what both non-amenable transfers consume: the tree fold, and the Ã2
Busemann transplant. For hierarchical fixed-point designs it is a ground-level layout rule ("information
flows up and right"), not an extra theorem.
