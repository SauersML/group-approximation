---
rg: 2
id: split-abelian-kernel-failure-proof
kind: route
title: Read the split failure off the mod-two member of the family
target: mf-fails-with-elementary-abelian-kernel
requires: [compression-wreath-five-radicals-coincide]
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/PermutationalWreath.lean
---

## Why sufficient

The sequence is split by construction: `W_{C2}` is a permutational wreath
product, so the projection to `G*` has the canonical section.

**Kernel.**  `A = C2^(G*/Gamma*)` is a restricted direct sum of copies of
`C2`, so it is abelian of exponent two.  Any finitely generated subgroup is
supported on finitely many sites, hence finite: `A` is locally finite, and a
finitely generated subgroup is its own Folner set, so `A` is amenable.  It is
residually finite because a nontrivial configuration is separated by
projection to any site where it is nontrivial, hence MF and MAP.  For
linearity, enumerate the sites and send a configuration `a` to the
unitriangular matrix with entry `sum a_i t_i` over `F_2(t_1, t_2, ...)`; in
characteristic two this is a homomorphism, and linear independence of the
`t_i` makes it injective.  (`PermutationalWreath.lean` carries the local
finiteness, residual finiteness, amenability, and linearity of the mod-two
lamp group at kernel level.)

**Quotient.**  `G*` embeds in `GL_4(Z[1/2])`, is residually finite by
reduction at an odd prime, hence MF and MAP.

**Middle.**  The prerequisite gives `Rad_MF(W_{C2}) = Res_fin(W_{C2}) =
Rad_lin(W_{C2}) = Rad_Bohr(W_{C2}) = R_{C2}`, and `R_{C2}` is nontrivial: for
two distinct sites `x, y` in the same height fibre — which exist because the
self-embedding is proper — the configuration lit exactly at `x` and `y` has
trivial parity on every fibre, so it lies in the kernel while being a
nontrivial element of the direct sum.  Therefore `W_{C2}` fails all four
properties.  Soficity is the finite-index telescope action plus the
generalized wreath theorem, and hyperlinearity follows from soficity.

## Priority

Failure of residual finiteness for split extensions of residually finite
groups is classical and is not claimed.  The MF instance with an
elementary-abelian kernel is the part worth a literature check before any
"first example" wording; the existing `mf-extension-nonclosure` already covers
plain non-closure with a nonabelian kernel.
