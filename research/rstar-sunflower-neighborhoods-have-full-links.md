---
rg: 2
id: rstar-sunflower-neighborhoods-have-full-links
kind: claim
title: Non-TVF sunflower neighborhoods cannot prune an R-star atom
distinct_from:
  distance-two-oracularity-does-not-force-fano-pruning: that gives one full-support countermodel; this is a general finite extension theorem identifying the incidence geometry which makes every neighborhood link nonempty.
  fano-pruning-is-line-hitting-empty-link: that turns an empty link into a zero atom; this proves that a broad class of local gadgets can never produce an empty link.
---

**ESTABLISHED SUNFLOWER FIREWALL.**  Let `c` be a distinguished `R_*`
context and fix `a in R_*`.  Partition a proposed neighborhood of `c` into
finite petal blocks `G_1,...,G_t`.  Assume

1. variables belonging to different blocks are disjoint outside `c`;
2. block `G_i` meets `c` in a coordinate set `T_i`; and
3. the restriction `a|T_i` extends to a satisfying assignment of every
   constraint in the whole block `G_i`.

Then

```text
Link(c,a) is nonempty.                                  (SUN1)
```

Indeed, choose one extension in each block.  The chosen assignments agree
with `a` on their intersections with `c`, and different blocks have no
other common variables, so their union is one jointly compatible
neighborhood assignment.

In particular, suppose every block is a single `R_*` petal and

```text
|T_i| <= 2.                                             (SUN2)
```

The projection of `R_*` onto any one or two coordinates is all of the
corresponding Boolean cube: the odd-parity equation has respectively four
or two completions, and deleting the one ghost removes at most one.  Hence
every `a|T_i` extends, so `(SUN1)` holds for **every** `a in R_*`, no matter
how many petals are added.  The same conclusion holds when a petal is
replaced by any finite pp block whose classical solution relation has full
projection onto `T_i`.

Consequently a line-hitting gadget cannot be obtained merely by attaching
fresh-private one- or two-coordinate checks around a context.  It must use
at least one of the following genuinely different resources:

```text
an effective overlap on at least three center coordinates;
shared auxiliary variables coupling different petals;
or a petal block whose visible projection already omits the target face.
                                                               (SUN3)
```

Mutual commutation of the petal algebras does not change this combinatorial
conclusion.  It permits a joint PVM once a link is empty, but cannot make an
independently extendable link empty.

