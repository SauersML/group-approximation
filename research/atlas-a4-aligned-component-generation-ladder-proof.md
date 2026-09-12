---
rg: 2
id: atlas-a4-aligned-component-generation-ladder-proof
kind: route
title: Enumerate each raw packet component against its reference-aligned conjugate over F2
target: atlas-a4-aligned-component-generation-ladder
requires:
  - atlas-shortest-a4-triangle-packet
  - atlas-a4-packet-biclique-decomposition
  - atlas-a4-packet-centralizer-product-compiler
artifacts:
  - experiments/atlas_a4_reference_alignment.py
---

The replay script is a finite exact `F2` calculation with no sampling and no
floating point.

It first recomputes the reference alignment itself.  Scanning the `20160`
inner alignments of `A8=GL4(F2)` against the thirty pair-cubes of
`atlas-shortest-a4-triangle-packet` leaves exactly `30` survivors, and the
alignment `R` fixed by `atlas-a4-packet-centralizer-product-compiler`,

```text
00000001000100000100000000000100,
```

is one of them, of order `3`.  This is the same `R` the compiler shifts by, so
the ladder is stated about the alignment actually in use and not about some
other packet solution.

It then rebuilds the label pair graph of the packet and splits it into its
connected components.  Per `atlas-a4-packet-biclique-decomposition` there are
two, carrying `4` and `6` labels.  For a component `C` the script forms three
subgroups by closed breadth-first multiplication inside `GL4(F2)`:

```text
raw     = <C>,
aligned = <R c R^-1 : c in C>,
joined  = <C, R C R^-1>,
```

and the intersection `raw ∩ aligned` by exact key comparison.  The measured
geometry is

```text
|C|=4:  |raw|=6,   |aligned|=6,   |raw ∩ aligned|=1,  |joined|=168,
|C|=6:  |raw|=18,  |aligned|=18,  |raw ∩ aligned|=1,  |joined|=20160,
```

which is `(ALIGN-COMP-1)` and `(ALIGN-COMP-2)`.  Both histograms are hard-coded
in the script as replay invariants and any deviation raises `AssertionError`,
so the certificate cannot pass while reporting different orders.

`168=|GL3(F2)|` and `20160=|A8|` are read off the enumerated closures
themselves; no group classification theorem is invoked to name them.  The
identification of `raw` with `S3` and `S3 x C3` is the cited biclique
decomposition's, not this route's -- here only the orders are measured.

### Scope

This route certifies a structural sharpening, not a step of any current
derivation.  It is used as prose in the attack plan of
`atlas-centralizer-products-19243-classicalize` (which large-component
coherence theorem would already be a full-chart synchronization, and why the
small `K_(2,2)` component is a rank-three calibration rather than the source of
chart generation).  No live route consumes it as a premise, and none should be
retrofitted to do so until an argument actually uses the ladder.
