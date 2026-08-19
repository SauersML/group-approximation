---
rg: 2
id: atlas-a4-componentwise-commutant-collapse
kind: claim
title: Collision 19243 forces the relative chart frame into both packet-component commutants
distinct_from:
  atlas-a4-relative-packet-commutator-collapse: that asks directly for vanishing commutators with all ten packet letters; this target splits the task into the S3 and S3xC3 component commutants exposed by the packet biclique decomposition.
  atlas-a4-alignment-moment-simplex-rounding: that asks only for scalar moment rounding to classical alignment mixtures; this target remains operator-valued but only on two small finite subgroup categories.
---

Let `sigma_n` satisfy the exact-regular normalized A4 context-network hypotheses
of `atlas-a4-holonomy-coherence-gap`, choose arbitrary regular frames for the
two `A8` chart vertices, and let

```text
U_n in U(20160 k_n)
```

be the resulting relative chart frame.  Let `H_6 ~= S3` and
`H_18 ~= S3 x C3` be the two packet-component subgroups from
`atlas-a4-packet-biclique-decomposition`.

Prove

```text
dist_2(U_n, lambda_(k_n)(H_6)')^2
+
dist_2(U_n, lambda_(k_n)(H_18)')^2
   -> 0.                                               (A4-COMP-COLLAPSE)
```

The statement includes the collision hypothesis `q_19243 -> 1` through the
ambient normalized-network assumptions.  Packet pair-cubes alone are not
expected to force this: the classical packet has surviving automorphism
alignments until collision `19243` is imposed.

## Attempts

- **Exploit the exact bicliques, not thirty unrelated contexts.**
  `atlas-a4-packet-biclique-decomposition` reduces the distinct pair graph to
  `K_(2,2) disjoint_union K_(2,4)`.  After the canonical A4 qutrit/multiplicity
  split, seek one `U(k_n)` edge message per distinct pair.  By
  `unitary-k2m-rectangle-synchronization`, all local noncommutative gauge
  inconsistency is then measured by only four rectangle holonomies.
- **Do the Fourier analysis on the two actual component groups.**  Their types
  are only `S3` and `S3 x C3`; compute the finite intertwiner spaces and the
  action of collision `19243` on the four rectangle variables.  The external
  multiplicity tensors out once the residuals are linear subspace-membership
  conditions.
- **Treat 19243 as the cross-component anchor.**  The packet components are
  disconnected at the pair-constraint level but their generated subgroups
  intersect trivially and together generate `A8`.  The useful identity should
  show that small collision defect prevents the two independently factorized
  biclique gauges from choosing incompatible chart alignments.
- **Do not return to the refuted three-word test.**  The exact `A5 x C2`
  countermodel proves that a tiny support can evade the desired gap.  Any
  certificate here must use enough of the full `K_(2,2) disjoint_union
  K_(2,4)` structure to exclude that coset-action escape.
