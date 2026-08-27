---
rg: 2
id: fanizza-private-hard-share-is-point-stabilizer-local
kind: claim
title: Realize the gauge-doubled Fanizza hard share as a point-stabilizer-local occurrence
distinct_from:
  gauge-weyl-fanizza-incidence-rounding: that attaches two-sided reset bridges throughout the original finite Fanizza incidence; this asks only for the private hard share used by the exit bridge to be a Thompson-site occurrence.
  finite-orbit-occurrence-pauli-compiler: that compiles an unbounded robust Pauli game; this is one fixed finite menu of Fanizza hard roles.
---

For the finite menu of gauge-doubled Fanizza Schur/mixed-CNOT hard frames, let
`H` be the finitely presented group-word system for one complete occurrence,
including all shared logical products **within that occurrence**, its private
hard shares, the common mark, and the context-local finite packets.  Apply
`thompson-free-occurrence-amalgam-preserves-contextuality` to `H`.

Then:

1. each level's private hard involution `A_x` is fixed by the point stabilizer
   of its site and the finite menu of roles gives only finitely many site
   orbits;
2. the invariant logical products of the two gauge shares still realize the
   original shared Fanizza BCS words and native signal inside each occurrence;
3. no identification of private shares at distinct sites forces two original
   logical variables from noncommon contexts to commute; and
4. the exact gauge-covariant marked representation is a site tensor model to
   which `point-stabilizer-local-hard-share-compiles-bridge-orbit` applies.

The construction uses a free, not commuting, occurrence product.  Thus clause
3 is literal: there is no relator involving two different occurrence groups
apart from their common central mark.  Point stabilizers fix the whole base
occurrence pointwise, proving clause 1.  Gauge covariantization and
`context-local-schur-packet-marked-extension`, followed by the free-product
marked representation (or simply the folding retraction for nontriviality),
prove clause 4.

This localizes the **whole finite occurrence**, not each original logical
variable separately.  It therefore does not assert that different recurrence
levels use one globally identical BCS tuple.  The active-return transporter
must carry the reducing active corner from one free occurrence to the next;
that is exactly the separate open claim `mixed-cnot-allowed-active-return`.

## Fences retained

- Putting the entire shared logical tuple into commuting lamp factors is
  invalid: it globalizes commutation across contexts.
- Keeping one logical tuple globally identical at every site would recreate
  the commutation problem.  The free occurrence construction deliberately
  avoids that assertion.
- This theorem closes only exit attachment.  It does not identify or return
  active corners between the free occurrences, and hence does not solve the
  full recurrence by itself.
