---
rg: 2
id: coherent-reselection-reduces-to-private-label-core
kind: claim
title: Coherent shadow reselection reduces to the private-label relation core
distinct_from:
  local-source-gauge-is-coherent-shadow-reselection: that identifies gauges with coherent reselection but constructs neither; this gives an explicit elimination algorithm and localizes the remaining synchronization obstruction.
  spherical-one-shared-map-relation-extension: that attaches a relation with only one previously assigned label; this also attaches a relation sharing two assigned labels whenever its third label is fresh.
  spherical-one-overlap-forest-rounding: that treats one-overlap relation forests; this treats every Tietze-peelable relation system, including incidence cycles and redundant closing relations.
  hypergraph-near-perfect-schreier-packing: that asks for a coupled packing for the whole relation hypergraph; this proves no coupled packing is needed outside a canonical private-label core.
---

Let `S` be a finite label set and let `R` consist of tested equations

```text
g h = k.
```

Encode such an equation by the relator `k^(-1)gh` in the free group
`F(S)`.  Choose a relation basis `R_0 subset R` such that every relator
from `R` lies in the normal closure of the relators from `R_0`.

A label is *private* in a current relation system if it occurs exactly once
in one relation and in no other current relation.  Repeatedly delete a
relation having a private label.  The relations left after no further
deletion form the **private-label core**.

Under the same-cloud spherical hypotheses of
[[spherical-short-holonomies-admit-local-gauge]], coherent shadow reselection
for `R_0` is quantitatively equivalent to coherent shadow reselection for
its private-label core:

1. a coherent family for the full system restricts to the core;
2. every coherent family on the core extends across all deleted relations on
   the same cloud, using only independent tight single-label matchings and
   exact composition or inverse composition; and
3. if the core shadow radius is `e`, the single-label matching radius is
   `rho`, and every unitary relation defect is at most `zeta` off an
   exceptional set of density `eta`, then the extension has shadow radius
   at most

   ```text
   C_T (e+rho+zeta)
   ```

   and exceptional density at most `C_T eta+o(1)`, for a constant depending
   only on the finite table.

After arbitrary completion of the partial bijections, every relation in
`R_0` has Hamming defect `o(1)`.  Every relation in `R` then also has
defect `o(1)), by bi-invariance of Hamming distance and the chosen normal
closure expressions.

In particular, every table admitting a relation basis with empty
private-label core has coherent same-cloud shadow reselection.  This strictly
extends one-overlap forests.  For example,

```text
a b = c,        a c = d
```

shares two labels in the second relation, but one may choose tight shadows
for `a,b`, define `c=ab`, and then define `d=ac`.

The theorem also handles genuine closing diagrams when the closing equations
are formal consequences.  For instance,

```text
a b=c,        c d=e,        b d=f
```

form an empty-core basis, and the fully old equation `a f=e` follows
automatically by associativity.

Thus Hall or hypergraph synchronization is needed only on the nonempty
private-label core.  The first unresolved relation is not one that merely
reuses two maps; it is a nonredundant relation all of whose labels survive
the peeling process.

DERIVATION
[[private-label-core-reselection-proof]]
