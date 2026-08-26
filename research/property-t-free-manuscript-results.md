---
rg: 2
id: property-t-free-manuscript-results
kind: claim
title: Reprove the non-MF manuscript endpoints without Property T
root: true
goal: true
artifacts:
  - non_mf_groups_exist.tex
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-audit.md
  - research/proposed-property-t-free-whitehead-proof-safe-prefix-route.md
---

**OPEN.**  Produce a replacement proof of the results advertised by
`non_mf_groups_exist.tex` in which Property `(T)` is absent from the proof,
not merely hidden behind a premise-free theorem.

The replacement must include the mathematical endpoints that remain after
removing the Kazhdan-specific intermediate language:

1. an explicit countable non-MF group, with a nontrivial element killed by
   every homomorphism to every norm matrix corona;
2. the full-MF-radical version for the binary-Leavitt group;
3. the basic MF-radical and MF-kernel-closure calculus;
4. functoriality, normal-generation saturation, full-kernel pullback, and
   universal factorization;
5. the explicit simplicity, defect, and prescribed-visible-quotient
   consequences used by the manuscript.

The final kernel-checked surface is

```text
GroupApproximation/Manuscript/OneSidedMFRadical/Unconditional.lean
```

and must have no declaration input standing for an unformalized literature
result.  Its proof dependency cone must not use a Property-`(T)` or Kazhdan
theorem.  In particular, a closed declaration obtained by instantiating
`HasKazhdanPropertyT` does **not** satisfy this claim.

The Kazhdan projection/order/transport statements in the current manuscript
are proof machinery, not endpoints to rename.  They must be removed from the
replacement argument and replaced by the finite-coordinate Property-`(T)`-free
mechanism that proves MF invisibility.

## Attempts

The downstream radical calculus is already algebraic and independent of
Property `(T)`.  The load-bearing missing input is the concrete
binary-Leavitt MF collapse recorded at
`property-t-free-leavitt-full-mf-radical`.  Writing a theorem package whose
only new premise is an authenticated return would be conditional and would
not settle this goal; the literal return compiler must first be proved.

### State on 2026-08-26 (evening)

The endpoint is now a single leaf.  With simplicity of `EL_n(R)`, the
torsion-normal-generator character criterion and conjugate tensor-power
Diracization, the full MF radical is equivalent to
`leavitt-regular-character-is-not-mf`: no operator-norm asymptotic
representation of the Leavitt group has all normalized traces tending to
zero (`property-t-free-el20-collapse-via-regular-character`).  Every
retained manuscript endpoint follows from that leaf and the algebraic
calculus already in the graph.

Established Property-`(T)`-free structure around the leaf:
`leavitt-one-compressor-defect-lies-in-amenable-subgroups` (the full
degree-zero core and the unipotent parabolic with one compressor and the
centralizer are amenable and carry the defect);
`corona-representations-are-exact-on-locally-finite-subgroups`
(coordinatewise exactness, exact compressor intertwiners, regular
satisfiability, norm-2 dichotomy);
`degree-zero-leavitt-core-characters-are-dirac-haar-mixtures` (every
character of the core is `w+(1-w)delta_e`, so every MF character has
exactly the Dirac--Haar profile on every degree-zero root);
`monomial-root-elements-are-conjugate-in-the-leavitt-group` (the same
constant on every monomial root of every degree);
`steinberg-group-is-the-colimit-of-its-finite-root-subgroups` and
`steinberg-group-is-glued-over-the-permutohedron` (a corona
representation is an `o(1)`-cocycle of exact finite-group representations
on the permutohedron complex, obstructed only by braid-hexagon holonomy).

What is proven to be insufficient: characters and root-module spectral
measures, finite-subgroup and partial-conjugation data, amenable
sub-configurations, corona `K_0`/`K_1` and Bott classes, gap-free
commutant rank counting, and blind numerical optimization of truncated
presentations (`research/artifacts/leavitt-defect-floor-experiment-2026-08-26.md`).
The only known engine for the hexagon holonomy is the spectral gap of the
finite links (Garland), which is where Property `(T)` originates for these
groups; a proof meeting this goal must supply a non-spectral invariant of
finite-dimensional approximants that the regular character violates.
