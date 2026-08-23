---
rg: 2
id: atlas-spectral-shrunk-intertwiner-certificate
kind: claim
title: Atlas defect forces its relative chart unitary into a linearly shrunk low-energy matrix space
artifacts:
  - research/artifacts/operator-scaling-shrunk-subspaces-2026-08-19.md
distinct_from:
  atlas-wedderburn-soft-transport-certificate: that selects scalar costs on whole Wedderburn blocks; this target may select low-energy singular directions inside blocks and asks for a noncommutative-rank/shrunk-subspace certificate instead of a classical transport cut.
  atlas-wedderburn-hall-deficient-support-certificate: that asks for a hard deficient bipartite block graph; this target is its operator-space refinement and can witness deficiency with non-coordinate subspaces.
---

There are constants `C,p,gamma>0` and a threshold rule `a(delta)>0`, with

```text
C delta^p / a(delta) -> 0 as delta -> 0,             (ASI1)
```

such that every sufficiently accurate finite-dimensional regular-`A_8` atlas
microstate of dimension `d` has the following certificate.

After exactifying the fixed finite chart packets, let `U` be the relative
chart unitary on the finite coefficient/multiplicity space.  Construct from a
fixed finite set of atlas conjugacy/intertwining relators a positive
semidefinite quadratic form

```text
E_delta(T)=<T,L_delta T>
```

on `M_d(C)` satisfying

```text
E_delta(U) <= C delta^p.                              (ASI2)
```

Let `K_delta` be the spectral subspace of `L_delta` for eigenvalues in
`[0,a(delta)]`.  Then there is a subspace `X_delta <= C^d` with

```text
dim X_delta - dim K_delta(X_delta) >= gamma d.        (ASI3)
```

The construction of `L_delta`, the spectral cutoff, and the certificate
`X_delta` may use the finite multiplicity data of the microstate; only the
relator menu and constants are uniform.

## Why this is a sharper finite-coordinate target

`(ASI2)` says the actual relative unitary is spectrally close to the low-energy
matrix space.  `(ASI3)` says that same matrix space loses a fixed fraction of
dimension on one input subspace.  By
`spectral-low-energy-shrunk-space-obstruction`, these two assertions are
incompatible with `(ASI1)`.

Unlike a fixed Hall support graph, the low-energy matrix space is allowed to
move with the microstate and to keep only selected singular directions inside
a block.  This is precisely the finite rank/spectral dependence that the
universal-factor no-go results leave open.

## Attempts

- **Block Laplacian.** Start with the same finite Wedderburn decomposition used
  by the soft-transport route, but retain the complete mixed-intertwiner
  quadratic form on each rectangular block instead of collapsing it to one
  scalar cost.  Threshold its spectrum at `a(delta)` and assemble the direct
  sum of low-energy eigenspaces.
- **Operator scaling as the separator.** Feed a certified finite basis of
  `K_delta` to a shrunk-subspace routine.  The relevant algorithmic literature
  is recorded in the attached artifact; any output `X_delta` is checked by
  finite linear algebra before it is used analytically.
- **Hall as a sanity check.** If the spectral spaces happen to be either whole
  blocks or zero, `(ASI3)` reduces to the existing weighted Hall certificate.
  Thus this route extends rather than contradicts the finite-transport work.
- **Falsification gate.** If numerical/exact finite experiments show that every
  threshold satisfying `(ASI1)` has only `o(d)` shrinkage, retire this route:
  the generic theorem shows no constant normalized-HS obstruction can then
  come from low-energy noncommutative rank alone.
- **The phase-cycle Jacobian is not the required Laplacian.**
  `atlas-phase-jacobian-has-invertible-gauge-kernel` differentiates the exact
  scalar symmetry `U -> exp(it)U`.  The tangent `iU` lies in the Jacobian
  kernel at every point and is invertible, so its complex operator space has
  no shrunk subspace at all.  Thus `L_delta` cannot be the ordinary
  Gauss--Newton/Jacobian form of the five boundary holonomies and interior
  holonomy.  A positive construction must pin/quotient that gauge without
  losing the actual unitary, or use a different mixed form.
- **One linear pin does not repair the Jacobian.**
  `atlas-one-functional-gauge-pin-cannot-create-shrinkage` shows that the
  honest phase slice `Im ell(T)=0` is real-linear; its complexification
  contains the invertible radial matrix `U` and cannot shrink.  The complex
  hyperplane `ell(T)=0` imposes an extra physical equation, while phase
  normalization is either uniformly stable and energy-neutral or unstable
  near `ell(U)=0`.  Any useful pin must therefore be authenticated by further
  mixed relations and must output a complex relative space by a mechanism
  stronger than deleting one scalar coefficient.
- **Cross-Jacobians do not pay the missing mode.**
  `atlas-cross-jacobian-cannot-pay-the-gauge-mode` shows that the nonlinear
  Jacobian kills `iU`, so every nonlinear--additive bilinear cross term also
  vanishes there.  A positive combined form either has no additive diagonal,
  in which case positivity kills the cross block, or charges `iU` by a
  quadratic expression in the additive circulation itself.  Controlling
  that expression by nonlinear defect is already the missing five-row
  inequality.  Thus a bilinear Hessian does not furnish an independent
  shortcut.
- **Full word data have a double-commutant gauge.**
  `atlas-full-relator-data-factor-through-double-commutant-gauge` audits the
  complete two-chart word list at once: `U` and `DUC`, for left/right chart
  commutant unitaries, give conjugate evaluations of every word.  Thus a raw
  multiplicity coordinate or singular vector cannot define `K_delta`.
  Gauge-legal candidates must be assembled from the simultaneous mixed
  blocks `P_i U Q_j`; only their equivariant range/principal-angle data
  survive.  This identifies the block-range Hall construction as the first
  admissible singular-space target rather than merely a convenient one.
