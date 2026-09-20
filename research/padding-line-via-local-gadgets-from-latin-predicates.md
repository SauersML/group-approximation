---
rg: 2
id: padding-line-via-local-gadgets-from-latin-predicates
kind: route
title: Dead -- cross the padding line with per-gadget-certified local gadgets from 3Lin, kLin or quasigroup predicates into unique games over any alphabet L >= q
target: unique-games-np-hard-below-the-padding-line
requires: []
---

**Dead.** This route reduces a Gap-CSP(H) at soundness `1/q + eps` into unique
games by local gadgets. `H` is any source predicate with a co-dimension-one
information set whose free coordinate is pairwise uniform with every other
coordinate. Examples are 3Lin and kLin over any abelian group, and quasigroup
equations. The primaries are encoded injectively into an output alphabet
`L >= q`, the output permutations are arbitrary, and soundness is certified
gadget by gadget.

It is killed by `gadgets-into-any-unique-games-stay-below-padding-line`.
* *Invariant:* the fibre-plurality score `σ` along the free coordinate. It is
  invariant under every relabelling, `1/N`-Lipschitz, `1` on the free primary
  and `1/q` on the others.
* *Step where every member dies:* soundness certification. A threshold switch
  on `σ`, between two uniform reading points, is equivariant and random on the
  primaries. Its deletion is at most `(2 - 1/N) c`, so `R <= 2 - 1/N < 2`.

This subsumes the fixed-point-limited kill `three-lin-gadgets-stay-below-padding-line`,
at a weaker constant. The survivors are those listed in the kill: Hadamard-type
predicates, sources below the `1/q` threshold (label cover, d-to-1), long-code
labels, and global certificates.
