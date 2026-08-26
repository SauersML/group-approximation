---
rg: 2
id: kt-double-reduced-cstar-is-mf
kind: claim
title: The reduced C-star algebra of the q=2 Kun--Thom double is MF
distinct_from:
  reduced-amalgam-canonical-trace-is-mf: that asks for operator-norm microstates selecting the canonical trace on the full group C-star algebra; this asks for a norm-corona embedding of the reduced group C-star algebra, after which the trace is selected automatically by uniqueness.
  symmetric-double-weak-mf: that embeds the abstract group, and in the proof a full auxiliary symmetric amalgam, into a norm matrix corona; neither conclusion says that the regular representation norm is approximated.
  kt-double-mixed-word-trace-selection: that is equivalent to hyperlinearity and controls normalized Hilbert--Schmidt moments only; reduced C-star MF additionally controls operator norms of every group-ring element.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
---

**OPEN.**  For the explicit Kun--Thom pair over `F_2`, put

```text
Gamma < G,                 D=G *_Gamma G.
```

Prove that `C*_r(D)` embeds into a norm matrix corona.

The target is stronger than hyperlinearity of `D`.  Its value is that the
reduced algebra has a unique tracial state: the `q=2` Bass--Serre calculation
in the cited artifact gives a faithful non-elementary tree action and trivial
amenable radical, so the BKKO theorem makes the canonical regular trace the
only trace on `C*_r(D)`.  Consequently any MF embedding of this reduced
algebra automatically induces the canonical trace in a tracial matrix
ultraproduct and makes `D` hyperlinear.

This is not supplied by residual finiteness of `G` or by Shulman's symmetric
full-amalgam theorem.  In particular, MF passes to C-star subalgebras, so the
claim already requires

```text
C*_r(G) is MF.                                             (KRC1)
```

Residual finiteness supplies group-level norm-corona separation and an MF
completion carrying an abstract regular trace; it does not supply `(KRC1)`.
The concrete profinite regular completion used in
`symmetric-double-weak-mf-proof` fails to factor through `C*_r(G)` by
`kt-shulman-profinite-vertex-model-is-nontempered`.

