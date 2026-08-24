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

**ESTABLISHED, PROPERTY-(T)-FREE, EXACT-ONLY.**  Let `R` have characteristic
`p` and carry a binary Leavitt family, and let `H(R)` be the Heisenberg group
on `R^3` with `[X(a),Y(b)] = Z(ab)`.  Work on a central-character sector `K`
where `Z(c)` acts by an additive character `lambda` with `lambda(1)` of order
`p`, and suppose an ambient actor `u` implements the first Morita branch on the
**entire** root group:

```text
u X(a) u^-1 = X(a t_0),   u Y(b) u^-1 = Y(s_0 b),   u Z(c) u^-1 = Z(c).
```

Decompose `K` into `X(R)`-character spaces `K_chi` with multiplicities
`m(chi)`, and let `F chi(a) = chi(a t_0)` be the branch pullback.

**The transverse shear.**  Put `y = pi(Y(s_1))`.  The Heisenberg law gives
`Y(s_1) X(a) Y(s_1)^-1 = Z(a s_1)^-1 X(a)`, so `y` carries `K_chi`
*unitarily* onto `K_(chi eta)` where `eta(a) = lambda(a s_1)^-1`.  Two
computations do everything:

```text
eta(a t_0) = lambda(a t_0 s_1)^-1 = 1      so  F(chi eta) = F(chi);
eta(t_1)   = lambda(t_1 s_1)^-1 = lambda(1)^-1,  of order p.
```

So `chi, chi eta, ..., chi eta^(p-1)` are `p` DISTINCT characters lying in one
`F`-fiber, all of equal multiplicity.  Hence

```text
m_branch(F chi) >= p * m(chi).                                   (MD-p)
```

**Global branch conjugacy closes it.**  Because `u` implements the branch on
the whole root group, the branch representation is unitarily equivalent to the
source, so `m(psi) = sum_(F chi = psi) m(chi)` and therefore

```text
m(F chi) >= p * m(chi).                                          (MD)
```

Taking a character of maximal positive multiplicity contradicts finite
dimensionality, since `p >= 2`.  So `lambda` occurs in no nonzero exact
finite-dimensional representation, and in particular the marked Leavitt defect
dies in **every exact finite-dimensional representation**.  In characteristic
two, with a marked central involution `Z(1)`, this kills the `-1` sector
outright, which is the doubling this node is named for.

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
