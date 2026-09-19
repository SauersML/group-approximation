---
rg: 2
id: scalar-bus-packet-couplings-retain-all-global-assignments
kind: claim
title: Scalar-bus couplings of predicate packets retain every global assignment in the marked clause face
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives one regular stationary type vector containing every selector atom, but its central predicate words need not have the marked clause phase; this constructs an exact finite-dimensional representation entirely inside the marked clause face and permits arbitrary prescribed global selector signs
  finite-packet-central-sign-cannot-enforce-nonlinear-support: that is the one-packet induction obstruction; this proves that joining arbitrarily many such packets around any finite Bass--Serre graph through scalar buses still cannot remove the induced bad sectors
  product-word-stabilizers-cannot-linearize-one-losing-corner: that preserves every vector in three allowed product rectangles and derives preservation of the fourth; this allows state-selected local packet types and instead proves that scalar cross-context transport cannot distinguish their unwanted companions
  central-word-state-face-compiler: that asks for a positive state-dependent global coupling; this excludes the entire scalar-edge graph-of-finite-packets subclass while leaving genuinely nonscalar payload coupling open
---

**ESTABLISHED.**  Let `Y` be a finite connected graph of finite groups.  Write
`K_v` for its vertex groups and `H_e` for its edge groups, with edge maps

```text
i_(e,v):H_e -> K_v,       i_(e,w):H_e -> K_w.          (SBP1)
```

Suppose that for every vertex `v` there is a nonzero finite-dimensional
unitary representation `pi_v:K_v -> U(V_v)` and, for every incident edge
`e`, a character `chi_e:H_e -> T` such that

```text
pi_v(i_(e,v)(h))=chi_e(h) I_(V_v)                     (SBP2)
```

for all `h in H_e`; at the other endpoint the same character occurs.  Then
the fundamental group `Pi=pi_1(Y)` has a nonzero finite-dimensional unitary
representation whose restriction to every `K_v` is a positive amplification
of `pi_v`.

This remains true for arbitrary cycles and HNN edges.  In particular, scalar
edge buses cannot use holonomy to delete a locally compatible collection of
vertex sectors.

## Proof

Let `d_v=dim(V_v)` and choose a common positive multiple `D` of all the
`d_v`.  Replace `pi_v` by

```text
Pi_v=pi_v^(direct sum D/d_v):K_v -> U(C^D).            (SBP3)
```

By `(SBP2)`, both embeddings of every edge group now act on `C^D` by the
same scalar representation `chi_e(h)I_D`.  Choose a maximal tree in `Y`.
The vertex representations therefore agree literally on every tree-edge
group and give a representation of the iterated amalgamated free product.
For every edge outside the tree, send its stable letter to `I_D`.  Its HNN
relations hold because its two edge images are again the same scalar
operators.  The universal property of the graph-of-groups fundamental group
gives the asserted representation.  End proof.

## Application to the central predicate-phase packets

For each BCS context `c`, let `K_c`, `z_(c,x)`, and `w_c` be the finite
packet and central words used in
`central-word-state-face-compiler`.  Fix a global Boolean assignment `a` to
the source variables.  The selected assignment-coordinate sector gives a
finite-dimensional representation with

```text
z_(c,x)=a_x I,       w_c=-I                           (SBP4)
```

when `a|U_c` is allowed.  When it is forbidden, the induced companion sector
`(CWA9)` gives a representation with exactly the same equations `(SBP4)`.
Thus **every** global assignment supplies one marked local sector at every
context.

Consider any proposed global coupling obtained from the context packets by a
finite graph of finite groups whose edge groups act in these sectors only
through the shared scalar selector/phase data.  This includes repeated-variable
amalgamation through the central selector subgroups, scalar phase routers,
and cycles or HNN stable letters which merely identify such buses.  Whenever
the edge maps respect the same global signs, `(SBP2)` holds.  The theorem
produces an exact finite-dimensional representation of the whole coupling in
which

```text
J=-I,       w_c=-I,       J w_c=I                     (SBP5)
```

for every predicate clause, even if every chosen context assignment is
forbidden.  Its vector states lie exactly in the marked target clause face,
so neither exact nor quantitative finite-dimensional soundness is possible.

The obstruction is stronger than exhibiting forbidden mass in a regular
representation: the representation `(SBP3)` has no wrong predicate phase at
all.  Cross-amplification removes the local dimension differences, and
scalarity removes every cyclic holonomy constraint.

Consequently the global coupling demanded by Properties 1 and 3 of
`central-word-state-face-compiler` must contain at least one relation whose
edge action is nonscalar on the local assignment sectors, or a genuine
two-cell constraining their multiplicity intertwiners.  Merely sharing more
selector signs, adding scalar phase routers, closing the incidence graph into
cycles, or adding scalar-edge HNN letters cannot exclude `(CWA9)`.  Such a
nonscalar coupling must still extend the state-conditioned tracial model
`(CWA5)`; this is the exact surviving payload-coupling problem.

