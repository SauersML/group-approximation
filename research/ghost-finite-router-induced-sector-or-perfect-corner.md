---
rg: 2
id: ghost-finite-router-induced-sector-or-perfect-corner
kind: claim
title: A ghost-completed finite router has either an induced ghost sector or a finite perfect common corner
distinct_from:
  ghost-completed-fano-naimark-wordizes-one-local-predicate: that constructs the desired controlled column in one chosen representation; this proves that no finite packet table authenticates that representation-specific correlation, and classifies what happens after a common Hecke corner is selected.
  finite-group-selector-induction-barrier: that proves the set of selector characters occurring somewhere is affine; this applies the induced ghost representation directly to any proposed local residual inequality and adds the common-corner alternative for a whole constraint instance.
  finite-morita-toricization-cannot-encode-nonaffine-support: that assumes a Morita equivalence carrying the answer algebra through centers; this needs no center identification and permits an arbitrary finite label group, arbitrary controlled routers, and a noncentral common projection commuting only with the decoded observables.
  packet-retraction-evaluates-hecke-collision-atlas: that assumes an ambient group retraction onto its finite packet; this obstruction already occurs inside the finite packet, before any ambient retraction is considered.
---

**ESTABLISHED FINITE-ROUTER FIREWALL.**  Let

```text
A=<z_1,...,z_m> isomorphic to (C_2)^m                  (GFR1)
```

be an affine-context selector subgroup of a finite group `K`.  The rest of
`K` may be an arbitrary finite nonabelian label/router packet.  Fix a ghost
character `chi_g in A-hat` and its atom

```text
e_g=|A|^(-1) sum_(a in A) conjugate(chi_g(a)) a
    in C[A].                                            (GFR2)
```

Then the exact finite-dimensional representation

```text
Ind_A^K(chi_g)                                          (GFR3)
```

has nonzero ghost atom.  Consequently every ordinary group relation true in
`K` has zero defect in a finite-dimensional model with `e_g!=0`.  In
particular no dimension-independent inequality of the form

```text
tau(e_g)<=C sum_j ||r_j-1||_2^2                         (GFR4)
```

can follow from the multiplication table, word relators, or finite Hecke
identities of `K`.

This applies unchanged after adjoining one shared finite label register and
an arbitrary deterministic controlled router on it.  The router may realize
the ghost-completed Fano Naimark column perfectly in one chosen block, but
the finite packet also has the induced block `(GFR3)`.  Thus its ordinary
relations do not authenticate the nonlinear correlation

```text
selector character = ghost
    iff
routing label carries the rejecting D8 type.            (GFR5)
```

There is only one finite-corner escape, and it closes in the wrong direction.
Let a finite `R_*` constraint instance have context selector subgroups
`A_c<=K`, ghost atoms `e_(c,g)`, and literally shared coordinate involutions.
Suppose a nonzero projection `q in C[K]` commutes with every decoded
coordinate involution and satisfies

```text
q e_(c,g)=0                         for every context c. (GFR6)
```

Then the finite-dimensional corner `q C[K]q`, with its normalized canonical
trace, is a perfect tracial strategy for the `R_*` instance.  Its context
atoms are `q e_(c,t)`, they sum to `q`, the ghost atom vanishes by `(GFR6)`,
and literal sharing gives one observable for every global variable.

Hence for a strict finite-dimensional-gap source, no finite packet can
simultaneously provide

1. one nonzero common input corner;
2. exact ghost removal in every context; and
3. literal cross-context variable compatibility.

If the selected projections are only contextwise, the conclusion does not
apply, but the original common-source seam remains.  If transporter
unitaries rather than literal compatibility are retained, the result is an
exact finite monomial transport model, not a BCS strategy, by
`finite-sheet-transport-networks-are-exactly-matricial`.

Thus ghost completion is valuable as a local Naimark dilation but does not
give a finite group/Hecke authentication of matrix soundness.  A successful
compiler needs a non-finite-packet relation which destroys the induced ghost
block while preserving the infinite perfect model, or a genuinely
matrix-only/canonical-trace coupling across contexts.
