---
rg: 2
id: congruence-modular-parabolic-triple-angle-gap
kind: claim
title: The modular elliptic--elliptic--parabolic projection triple has a uniform congruence angle
artifacts:
  - experiments/iwahori_parabolic_split.py
  - experiments/iwahori-parabolic-split.json
  - experiments/iwahori_parabolic_regular.py
  - experiments/iwahori-parabolic-regular.json
distinct_from:
  iwahori-cuspidal-hecke-angle: that bounds the angle between two Iwahori degeneracy maps on the kernel of parabolic restriction; this bounds the nonzero singular values of parabolic restriction itself.
  iwahori-eisenstein-angle: that compares the two opposite vertex residue maps after boundary classes have been extracted; this supplies a uniformly bounded extraction/lift inside each vertex.
---

For every finite-dimensional unitary congruence module `M=Ad rho` of
`PSL_2(Z)`, put

```text
K=ker(P_(C2)) cap ker(P_(C3)).
```

**ESTABLISHED.**  There is a constant `c>0`, independent of the quotient, `rho`, and its
dimension, such that every nonzero singular value of

```text
P_(<u>) | K : K -> M^u                                  (CPT1)
```

is at least `c`.  Equivalently, the angle between `K` and the parabolic fixed
space, after removing their orthogonal kernel, is uniformly positive.

## Attempts

- `modular-parabolic-restriction-is-a-three-projection-angle` proves that
  `(CPT1)` is exactly the uniform parabolic/Eisenstein splitting constant;
  no inverse of `1-u` occurs.
- **Bounded MSI screen, 2026-08-21.**  For
  `rho` the permutation representation on `P^1(F_p)` and coefficients
  `Ad rho`, the smallest nonzero singular values of the actual fixed-generator
  cocycle restriction map are

  ```text
  p       3      5      7      11     13     17     19     23
  sigma  .667   .429   .455   .483   .491   .502   .507   .514
  ```

  while the kernel grows from zero to dimension `74`, as expected for the
  cuspidal subspace.  There is no sign of the feared `1/p` decay in this
  family; the floor rises toward roughly one half after the small levels.
- **Expected proof mechanism.**  Decompose a congruence module into
  automorphic irreducibles.  The three projections are averaging idempotents
  for the elliptic stabilizers of orders two and three and the parabolic
  stabilizer.  This anticipated Selberg mechanism is realized more directly
  by `selberg-tau-proves-modular-parabolic-triple-angle`: on a parabolic-fixed
  vector the two elliptic generator displacements coincide, so ordinary
  congruence property `(tau)` is exactly the required lower bound.
- **Regular-representation stress test.**  The full regular modules of
  `PSL_2(Z/m)` contain every irreducible sector.  The computed floors are
  `.816,.526,.558,.577,.591,.601,.526` for
  `m=3,5,7,9,11,13,15`; the composite level `15` reproduces the worst local
  floor rather than multiplying losses.  These numbers are checks on the
  exact proof, not its basis.
