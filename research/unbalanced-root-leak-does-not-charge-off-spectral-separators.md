---
rg: 2
id: unbalanced-root-leak-does-not-charge-off-spectral-separators
kind: claim
title: Maximal unbalanced root leakage can coexist with a fully off-spectral positive matrix-range separator
invalidates:
  - sl3-fdg-via-unbalanced-root-leak-energy
artifacts:
  - research/unbalanced-root-leak-off-spectral-countermodel-proof.md
distinct_from:
  unbalanced-torus-word-localizes-britton-leak: that proves a dimension-free leak on one of two negative simple roots in every canonical arithmetic HNN packet; this gives an exact four-dimensional countermodel showing that the leak, even when maximal and aligned with the separator coordinate, does not by itself pay a matrix-range gap.
  hnn-matrix-range-obstruction-is-a-letter-multiplicity-coupling: that forces every canonical positive separator to have definite mass outside the stable-letter spectral algebra; this realizes full off-spectral mass and positive gap simultaneously with the unbalanced leak.
  sl3-hnn-finite-window-central-dual-gap: that may still use every approximate SL3 relator and canonical mixed moment; this only rules out a universal local inequality assembled from the unbalanced-word defect, root-leak energy, stable-letter centrality, and off-spectral separator mass.
---

**ESTABLISHED LOCAL FIREWALL.**  There is a four-dimensional unitary packet
for which all scalar inputs furnished by
`unbalanced-torus-word-localizes-britton-leak` are sharp:

```text
eta_R=eta_L=eta_B=0,       eta_21=2.                    (RLC1)
```

On the same packet there is a normalized coefficient tuple `C` which
commutes with the stable letter, is entirely orthogonal to its intrinsic
spectral algebra, and has matrix-range separation gap exactly one:

```text
sum_s ||C_s||_2^2=1,       max_s ||C_s||_op=1,
E_(W*(T))(C_s)=0,
Delta(C;X)=1.                                           (RLC2)
```

The nonzero coefficient is on the very coordinate carrying the maximal
root leak.  Thus neither coordinate support nor a missing quantitative
constant is the issue: even perfect alignment of the leak and the
off-spectral separator does not manufacture a ucp comparison point or
force its support function upward.

The construction uses the matrix range of the dihedral group of order
sixteen, not `SL_3(Z)`.  Its bad root coordinate deliberately violates an
involution relation.  Consequently this does **not** refute
`sl3-hnn-finite-window-central-dual-gap`.  It proves the precise no-go needed
at the new seam: `(UBL1)--(UBL4)` and `(LMC1)`, treated only as local norm and
support-function inequalities, cannot be coupled to close FDG.  A valid
coupling theorem must use further approximate `SL_3` relations (or an
equivalent actor-covariant matrix-order statement) to turn the leaking root
coordinate into a ucp point.

Proof: `unbalanced-root-leak-off-spectral-countermodel-proof`.
