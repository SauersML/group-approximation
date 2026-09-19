---
rg: 2
id: countable-tracial-amalgam-extension-proof
kind: route
title: Iterate reduced amalgamated free products and take the trace-preserving union
target: countable-tracial-amalgam-extension
requires: []
---

Finite dimensionality of `D_n` gives the unique trace-preserving conditional
expectation from either adjacent finite algebra onto the chosen copy of
`D_n`.  Form the reduced amalgamated free product at stage `n`; its vacuum
expectation is trace preserving and restricts to the old trace on both
factors.  The canonical embeddings are normal and trace preserving.

Inductively this produces a nested sequence of finite tracial von Neumann
algebras.  Its algebraic union has a consistent faithful trace; the GNS weak
closure is the required countable product.  Reduced freeness also says that
alternating centered words from distinct new factors have trace zero, which
is exactly the absence of unintended cross-stage selector relations.
