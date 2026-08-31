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

OPEN. For every finite-rank free **group** `F`, every decomposition
`F=A*B` into two nontrivial free factors, every cyclically reduced word `v`
of free-product syllable length at least two that is not a proper power, and
every `m>=1`, does

    G=F/<<v^m>>

admit a homomorphism to an amenable locally indicable group that is nontrivial
on every proper nonempty contiguous subword of the fixed cyclic spelling of
`v`?

The free-group hypothesis is essential. If arbitrary finitely generated
factors were allowed, `F=C_2*C_2`, `v=ab`, and `m=1` would be a
counterexample: the quotient is `C_2`, and locally indicable groups are
torsion-free, so both one-letter packet elements die. The claim here is only
the one-relator free-group question.

This is a finite, presentation-local weakening of residual amenability.  By
[[proper-subword-amenable-visibility-criterion]] it is sufficient for
soficity.  For a torsion-free group with nontrivial Linton radical,
[[linton-radical-has-a-short-weinbaum-marker]] shows that the canonical
residually-rationally-solvable quotient cannot be the required quotient: it
must kill at least one member of the packet.

[[li-weinbaum-visibility-is-relator-power-independent]] shows that the answer
is independent of `m`: every map to a locally indicable group kills `v`, so
the torsion presentation gives exactly the same quotient problem as
`F/<<v>>`.  [[rational-solvable-weinbaum-visibility-boundary]] sharpens the
remaining gate: a rationally solvable target retains the packet exactly in the
trivial-Linton-radical case.  Hence the unresolved case requires an amenable
locally indicable image outside the rationally solvable class; in the
perfect-radical subcase the image must be genuinely nonsolvable.

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
4. **Exploit the torsion exponent.**  *Exactly no extra freedom.*  By
   [[li-weinbaum-visibility-is-relator-power-independent]], every locally
   indicable target is torsion-free and therefore turns `v^m=1` into `v=1`.
5. **Stay within rationally solvable targets.**  *Complete boundary known.*
   [[rational-solvable-weinbaum-visibility-boundary]] proves that this works
   if and only if the Linton radical is trivial.  In the complementary case a
   proper-subword marker lies in that radical and every such target kills it.
6. **Use the explicit exponential-germ quotient of Baumslag--Gersten.**
   *Concrete hard-class candidate, two gates still open.*  Nyberg-Brodda,
   arXiv:2606.27408v1 (August 24, 2026 version), proves that `a->(x|->2x)`
   and `b->(x|->2^x)` gives a nonfaithful germ representation.  Its image sees
   `a`, hence sees the perfect radical and is nonsolvable; as a subgroup of the
   left-orderable group of germs at infinity it is left-orderable.  The paper
   does not prove that this image is amenable, and full proper-subword packet
   retention is also not established.  Thus it supplies exactly the right
   kind of candidate, but not a solution of this claim.

## Closed presentation-visible subfamily

[[abelian-weinbaum-packet-criterion]] gives a decidable positive family.  If
no proper subword's exponent-sum vector lies in the saturated rational line
spanned by the relator's exponent-sum vector, one homomorphism to `Z` retains
the whole packet.  The same lattice condition is necessary for every
torsion-free abelian target.
