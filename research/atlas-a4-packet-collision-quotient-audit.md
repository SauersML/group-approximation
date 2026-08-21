---
rg: 2
id: atlas-a4-packet-collision-quotient-audit
kind: claim
title: The exact A4 packet-collision quotient gives a finite stability-or-countermodel fork
artifacts:
  - experiments/atlas_a4_packet_19243_quotient.py
distinct_from:
  atlas-a4-gl5-packet-collision-screen: that exhausts embeddings of the two chart copies in one specific finite overgroup; this asks for the abstract quotient of the two-chart free product by the packet and collision words.
---

Put

```text
Q_A4 = (A8 * A8) / << thirty shortest A4 pair-cubes, q_19243 >>.
```

The exporter `experiments/atlas_a4_packet_19243_quotient.py` emits an exact GAP
presentation of `Q_A4`, the sizes of the two factor images, and four aligned
bridge tests.  Its outcome has the following rigorous interpretation.

1. Each factor image is either trivial or isomorphic to `A8`, because `A8` is
   simple.
2. If `Q_A4` is finite and one factor image is trivial, no exact
   representation of `Q_A4` has regular restrictions on both chart factors.
   Finite-presentation word filling followed by finite-group flexible HS
   stability then gives a positive normalized-HS gap for the exact-regular A4
   necessity sequence.  This closes `atlas-a4-holonomy-coherence-gap` without
   reconstructing the thirty context gauges.
3. If `Q_A4` is finite and both factor images survive, `Reg(Q_A4)` restricts
   to `[Q_A4:A8] Reg(A8)` on each factor.  It is therefore an exact
   regular-margin packet-plus-collision model.  Since the classical
   automorphism audit has no packet-plus-collision alignment, the two factor
   images cannot be the same subgroup related by an automorphism.  This gives
   a concrete nonclassical finite multiplicity mode which any proposed A4
   Dirichlet ceiling must confront; in particular it refutes any claim that
   the packet and collision force complete chart alignment in all exact
   regular-margin models.

Thus a bounded quotient computation is not merely a heuristic search.  A
finite quotient either closes the exact-regular obstruction or returns the
smallest possible exact countermodel stratum.

## Run status

The exporter itself completed on MSI and produced the GAP input.  The cached
GAP executable requires `GLIBC_2.29`, while both the Sioux and Agate nodes
provide an older glibc; the five-minute batch probe therefore failed in four
seconds before GAP started.  No rebuild or container pull was attempted.  The
quotient order and factor-image sizes remain uncomputed.

