---
rg: 2
id: one-relator-weinbaum-packet-amenably-visible
kind: claim
title: Every one-relator Weinbaum packet survives in one amenable locally indicable quotient
distinct_from:
  one-relator-groups-sofic: that asks for finite permutation approximations of every finite multiplication table; this asks only for one exact amenable quotient retaining the finitely many proper subwords of the defining relator, and is a sufficient but not asserted necessary mechanism.
  linton-radical-free-action-sofic: that asks for compatible approximate models of an automorphism action on the entire nonabelian radical; this asks for exact visibility of one finite packet in a possibly unrelated amenable quotient.
  residually-rationally-solvable-one-relator-sofic: that is an established theorem under a global residual hypothesis; this is a proposed universal finite-packet statement allowing non-solvable amenable quotients and is open precisely for nontrivial Linton radicals.
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

OPEN.  For every finite-rank free product `F=A*B`, every cyclically reduced
word `v` of free-product syllable length at least two that is not a proper
power, and every `m>=1`, does

    G=F/<<v^m>>

admit a homomorphism to an amenable locally indicable group that is nontrivial
on every proper nonempty contiguous subword of the fixed cyclic spelling of
`v`?

This is a finite, presentation-local weakening of residual amenability.  By
[[proper-subword-amenable-visibility-criterion]] it is sufficient for
soficity.  For a torsion-free group with nontrivial Linton radical,
[[linton-radical-has-a-short-weinbaum-marker]] shows that the canonical
residually-rationally-solvable quotient cannot be the required quotient: it
must kill at least one member of the packet.

## Attempts

1. **Use the canonical Linton quotient.**  *Fails exactly on the new marker.*
   If the radical is nontrivial, the short-marker theorem proves that this
   quotient kills a proper subword.  Composing it with rationally solvable
   quotients cannot repair the loss.
2. **Add successive rational-solvable lamp kernels over the canonical
   quotient.**  *Provably dead.*
   [[rational-perfect-core-blocks-rrs-kernel-lifts]] shows that every such
   exact lift still kills the entire rationally perfect radical.
3. **Use residual amenability.**  *Sufficient but deferred.*  Residual
   amenability would separate the finite packet in a finite product of amenable
   quotients, but Arzhantseva's stronger question whether all one-relator
   groups are residually amenable remains open; in particular the
   Baumslag--Gersten regime is unresolved by that method.  The claim here is
   deliberately weaker and may admit a packet-specific construction.
