---
rg: 2
id: self-hashing-expander-collision-presentation
kind: claim
title: One finite presentation self-hashes an unbounded packet/expander challenge family with exact infinite completeness
root: true
distinct_from:
  self-similar-clifford-quantum-expander-tape: that asks for uniform expander words on nested Clifford prefixes; this additionally requires depth-independent packet and cross-edge authentication, a finite cyclic verifier, and an exact nontrivial marked model in one presentation.
  free-cone-shift-finitely-wordizes-recursive-clifford-tails: that gives area-one addressed recursion and exact tail completeness but does not authenticate arbitrary cross-packet challenge edges or an expander checksum.
  authenticated-opnorm-challenge-compiler: that compiler is already established by seeding an existing MF-radical word; this is the stronger seed-free finite-capacity implementation target.
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
---

Construct a finite presentation with a marked phase `J` and all of the
following interfaces.

1. A fixed Pauli/Clifford packet exists at every virtual address.
2. Finite-state recursion generates challenge graphs of unbounded chromatic
   number, or equivalently Clifford prefixes of unbounded finite capacity.
3. Every addressed packet, transition, cross-edge, and checksum check is a
   literal conjugate of finitely many root checks, or has a common
   depth-independent operator-norm defect constant.
4. A fixed number of self-similar word templates has a uniform quantum
   expander gap on every active Clifford prefix.
5. Packet, address, and challenge authentication close in a finite verifier
   cycle.
6. An exact infinite-dimensional representation satisfies the presentation
   and keeps `J!=1`.

This is **OPEN**. Existing finite Pauli addressing, free-cone wordization, and
relative expander rounding do not yet establish their simultaneous
depth-independent composition. Polynomial derivation cost is insufficient.

## Attempts

- The free-cone shift makes recursive tail checks literal conjugates of root
  checks, but it does not authenticate arbitrary cross-packet edges.
- The oligomorphic Pauli addresser supplies every finite packet and an exact
  infinite model, but its stabilizer fillings cannot have uniform bounded
  area.
- The relative quantum-expander cell theorem removes dependence on old
  Clifford rank once expander words are supplied, but the self-similar
  constant-template expander tape is still open and current polynomial word
  transport does not satisfy the self-hash constant.
