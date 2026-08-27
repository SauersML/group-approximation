---
rg: 2
id: normal-state-free-near-representation-forces-factorization
kind: claim
title: A free near representation carried by a normal invariant state already has Kirchberg factorization
distinct_from:
  hyperlinear-near-representation-criterion: that permits an arbitrary state on B(H), including singular states, and characterizes hyperlinearity; this proves that the normal-state subcase collapses to a genuine representation and therefore belongs to the strictly stronger factorization regime.
  binary-leavitt-unit-group-fails-factorization-property: that is a property of one explicit group; this is a general structural theorem about normal-state near representations.
---

Let `G` be a group, `H` a Hilbert space, `phi` a **normal** state on `B(H)`,
and `pi:G -> U(H)` a `phi`-near representation in the sense of
Kahl--Schneider Definition 5.3(c).  Assume the induced character is the regular
character,

```text
phi(pi(g))=0                    for every g != 1.       (NSN1)
```

Then `G` has Kirchberg's factorization property.

The point is that a normal state cannot hide a multiplicative defect on a
finitely additive null set.  Writing `phi(a)=Tr(Da)` with `D>=0` trace class,
invariance forces every `pi(g)` to commute with `D`.  If `p=supp(D)`, the
near-representation defect vanishes on the dense range of `D^(1/2)` in `pH`,
so `pi|_(pH)` is an honest unitary representation.  The same state remains
invariant and still has regular character there.  Kahl--Schneider Theorem
7.4 then gives the factorization property.

Thus every genuinely hyperlinear-but-nonfactorizable group must use a
**non-normal** invariant state in the state-form near-representation
criterion.  This is a sharp qualitative firewall: trace-class density
operators, finite convex combinations of vector states, and any other normal
state cannot witness the gap between hyperlinearity and factorization.
