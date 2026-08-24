---
rg: 2
id: prefix-central-reducing-hull-recombines-context-returns
kind: claim
title: A pulse-central reducing hull recombines returned context ranges without aligning multiplicity gauges
distinct_from:
  shared-bcs-active-recombination-after-schur-returns: that applies this hull operation to all returned Schur child charts of the fixed BCS; this is the general analytic lemma.
  single-selected-atom-escape-compiler: that adjoins an escaped projection to grow a carrier; this takes several independently gauged returned ranges and preserves only one baseline copy inside a fixed positive prefix.
  fixed-packet-correction-retains-multiplicity-gauge: that records the arbitrary external gauge left by local packet correction; this proves that the gauge is irrelevant when coincidence of returned ranges is replaced by their common reducing hull.
---

**ESTABLISHED.**  Let `T` be a finite elementary-abelian packet of commuting
involutions, let `C in C[T]` be a projection, and let

```text
Y={y_1,...,y_s}
```

be a finite unitary tuple commuting with `T`.  Suppose
`P_1,...,P_l<=C` are projections and

```text
tau(P_j)>=q-epsilon_j.                                  (PCR1)
```

Let `Q` be the projection onto the smallest common reducing subspace for
`Y` which contains every `Ran(P_j)`.  Then

```text
P_j<=Q<=C,                 tau(Q)>=q-min_j epsilon_j.   (PCR2)
```

If the same literal generator `y_v` occurs in several context subtuples,
all context marginals on `Q` agree automatically: they are the spectral
cuts of the one compression `Qy_vQ`.  No identification of the external
multiplicity gauges of the `P_j` is required.

There is a dimension-independent normalized-Hilbert--Schmidt version for a
fixed presentation.  First exactify the finite packet `T`.  Average each
approximately commuting shared generator over `T`, polar-correct it inside
`T'`, and spectrally round the finitely many involutions.  This changes the
tuple and every fixed context polynomial by at most `C_0 sqrt(E)`.  After
the fixed finite context charts are aligned on their common shared
subgroups, their returned projections satisfy

```text
P_j<=C,                    tau(P_j)>=q-C_1 sqrt(E).     (PCR3)
```

Taking the reducing hull for the corrected global tuple therefore gives

```text
Q<=C,                      tau(Q)>=q-C_1 sqrt(E),       (PCR4)
```

with constants independent of the matrix dimension.  Enlarging the hull
can only improve the trace lower bound.  It cannot absorb an earlier
first-hit exit because those exits are orthogonal to `C`.

Proof: `prefix-central-reducing-hull-proof`.

