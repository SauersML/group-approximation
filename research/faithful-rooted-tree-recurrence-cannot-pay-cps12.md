---
rg: 2
id: faithful-rooted-tree-recurrence-cannot-pay-cps12
kind: claim
title: A faithful rooted-tree recurrence has exact finite-level countermodels to CPS12
distinct_from:
  two-qubit-pauli-automorphic-cell-has-collapse-or-stationary-flow: that treats finite graphs of finite packet groups and uses virtual freeness; this treats arbitrary faithful level-preserving rooted-tree recurrences, including infinite-state and non-Bass--Serre arithmetic actors.
  finite-stencil-pauli-tape-has-marked-periodizations: that constructs cyclic models for a bounded translation stencil; this simultaneously separates every fixed group-word window by finite tree levels.
  contracting-self-similar-checksum-has-finite-deep-state: that bounds the section alphabet of a contracting action; this needs neither contraction nor finite-state sections and gives canonical regular traces on finite windows.
  single-denominator-borel-cuts-have-a-rohlin-escape: that gives asymptotically invariant cuts for one amenable denominator action; this gives exact zero-relator finite models for every faithful synchronous tree action.
---

Let `Gamma` act faithfully by level-preserving automorphisms of a locally
finite rooted tree `T`.  Let `K<=Gamma` be a finite packet group and let
`0!=F in C[K]` be a projection, such as the uncovered forbidden projection
in the negative D8/Pauli sector.  For every finite set

```text
W subset Gamma\{1}                                    (RTR1)
```

there is an exact finite-dimensional representation `rho_W` such that

```text
tr(rho_W(w))=0                    (w in W),
tr(rho_W(F))=tau_K(F)>0,                              (RTR2)
```

and every defining relator of `Gamma` has zero defect.

Consequently no dimension-free finite-HS return inequality

```text
c tr(F(U))
 <= sum_(r in R_0)||r(U)-1||_2^2
    +sum_(w in W_0)|tr(w(U))|+o(1),       c>0,         (RTR3)
```

can follow from a finite presentation and a faithful rooted-tree recurrence,
where `R_0` and `W_0` are finite and the words in `W_0` are nonidentity.
The same conclusion holds with any finite list of fixed group-algebra
polynomials which vanish in exact representations in place of the relator
sum.

This applies to synchronous self-similar groups, finite automata groups,
branch recurrences, and arithmetic recurrences implemented by permutations
of every finite level.  It is independent of whether the section set is
finite, whether the action is contracting, and whether `Gamma` is virtually
free.  In particular, a level-preserving self-similar controller cannot turn
the Pauli forbidden kernel into the finite-only rank loss required by
`(CPS12)`.

The boundary is sharp.  A surviving self-similar mechanism must cease to be
a faithful action by automorphisms of the rooted levels.  It must use an
asynchronous prefix replacement or other unequal-index correspondence which
maps one cylinder onto a proper union of cylinders.  Even then, its
containment/rank inference cannot be a universal group-algebra identity,
which would hit the regular-trace firewall.  Thus the minimum remaining
ingredient is a non-level-preserving capacity gate with matrix-only source
authentication; synchronous recursion, however complicated, is excluded.
