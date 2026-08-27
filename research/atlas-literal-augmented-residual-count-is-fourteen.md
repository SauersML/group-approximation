---
rg: 2
id: atlas-literal-augmented-residual-count-is-fourteen
kind: claim
title: The literal two-chart augmented Atlas system has fourteen residuals, while the virtually-free carrier has thirteen fillings
distinct_from:
  atlas-thirteen-vf-fillings-are-tietze-irredundant: that proves irredundancy of twelve stable-letter fillings and collision after q14 is absorbed in the carrier; this reconciles that count with the literal relative presentation over the two chart groups.
  atlas-a4-packet-biclique-decomposition: that counts twelve distinct packet edges; this adds q14 and collision and tracks the change of ambient presentation.
---

ESTABLISHED.  There are two related, but different, relator counts.

Over the literal two-chart carrier `A8*A8`, the augmented quotient has the
relative presentation

```text
<A8,A8 |
  twelve distinct packet pair-cubes,
  q14=[t23_1,t23_2],
  q_19243>.                                           (LRC1)
```

Thus a defect space defined directly on a pair of repeated-natural chart
modules has **fourteen** named residual images.

In the graph-of-finite-groups carrier `Pi`, q14 is already exact: it is the
relation carried by the central `V4` bridge in the chosen maximal tree.  The
remaining filling list consists of the twelve non-tree stable letters and
collision, hence has **thirteen** entries.  Therefore

```text
fourteen literal A8*A8 residuals
       = q14 + thirteen post-carrier filling residuals. (LRC2)
```

The number thirteen may not be used for the residual-rank sum on an arbitrary
two-chart module unless q14 has first been imposed exactly and the module has
been lifted to the virtually-free carrier.  In particular, the elementary
rank estimate for the literal Morita formulation is

```text
dim D <= 14 epsilon dim E,                            (LRC3)
```

not `13 epsilon dim E`.  This changes no asymptotic conclusion, but it keeps
the ambient module category and the claimed residual formulas consistent.
