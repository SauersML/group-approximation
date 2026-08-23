---
rg: 2
id: finite-face-flatness-stops-at-fundamental-group-holonomy
kind: claim
title: Face-flat unitary connections retain exactly the fundamental-group representation holonomy
distinct_from:
  a3-cone-repairs-to-coboundaries-not-cocycles: that audits one simply connected spherical-building cone theorem; this gives the exact spanning-tree classification for every finite two-complex and identifies its quantitative repair problem with presentation stability.
  three-chart-loop-retains-free-multiplicity-holonomy: that inserts one arbitrary spectator on an abstract three-chart loop; this classifies all simultaneous face-flat loop data on an arbitrary finite incidence complex.
  compact-hyperbolic-km-regular-microstates-synchronize: that asks native Kac--Moody relations to correct canonical regular microstates; this proves that a lemma using only unitary edge gauges and Curtis--Tits face curvature is not a smaller synchronization theorem.
---

**ESTABLISHED.**  Let `X` be a finite connected two-dimensional CW complex,
choose an orientation of its edges, and assign `U_e in U(d)` with
`U_(bar e)=U_e^*`.  Vertex gauges act by

```text
U_e -> G_(t(e)) U_e G_(s(e))^*.
```

Call the connection face-flat when the ordered product around every attached
two-cell is the identity.  Gauge classes of face-flat connections are in
natural bijection with

```text
Hom(pi_1(X),U(d)) / U(d),                              (FFH1)
```

where `U(d)` acts by simultaneous conjugation.

Consequently face equations alone do not force a pure gauge.  Every
nontrivial finite-dimensional representation of `pi_1(X)` gives an exact
zero-curvature connection which is not gauge-equivalent to the identity.
More quantitatively, after fixing a spanning tree, the non-tree edge
unitaries are presentation generators and the face holonomies are exactly
the presentation relators.  Therefore a dimension-independent theorem which
repairs small face curvature to a flat connection is precisely normalized-HS
stability of that finite presentation, up to constants depending only on
`X`; a theorem which repairs to a pure gauge is the corresponding stability
statement restricted to the trivial representation branch.

For a Curtis--Tits or triangle-of-finite-groups diagram, this applies verbatim
to any extracted common regular multiplicity reservoir on which the finite
label action is trivial.  Local spherical-residue or single-face
synchronization can remove contractible gauge data, but the remaining flat
multiplicity connection is the global fundamental-group holonomy.  If the
edge transports instead twist the reservoirs by nontrivial label
automorphisms, those twists are additional coefficient data and lie outside
the bare face-curvature setting.  Any successful smaller lemma must use such
a native label--multiplicity coupling.
