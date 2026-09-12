---
rg: 2
id: simple-alternating-shift-no-go-proof
kind: route
title: Use finite level actions and rigidity of the isomorphism types of alternating factors
target: simple-alternating-limit-excludes-standard-self-similar-shifts
requires: []
---

Let `K` be simple and act faithfully on a locally finite rooted tree.  For
every level `d`, the level stabilizer is the kernel of a homomorphism from
`K` to the finite symmetric group of that level, hence is normal in `K`.
If all level actions are trivial then the tree action is trivial, contrary to
faithfulness.  Some level action is therefore nontrivial.  Simplicity makes
its kernel trivial, embedding `K` in a finite symmetric group.  Hence `K` is
finite.  This proves the first assertion.

For the second assertion, `(SAS1)` induces an isomorphism

```text
Gamma/ker q_(i+1)  ~=  Gamma/ker q_i,
```

and therefore `Alt(n_(i+1)) ~= Alt(n_i)`.  Alternating groups of degrees at
least seven are isomorphic only when their degrees agree, so an exact kernel
shift cannot follow an unbounded-degree sequence.  The same argument applies
to coordinate shifts: each finite alternating factor is a finite nonabelian
simple normal factor, and a coordinate-permuting automorphism can move it
only to an isomorphic factor.  End proof.
