---
rg: 2
id: modular-machine-halting-invariance
kind: claim
title: The three modular-machine facts the group construction consumes
artifacts:
  - GroupApproximation/Computability/BooneGroupModularMachine.lean
---

ESTABLISHED, for an arbitrary modular machine, with no group theory in it.
`Computability.BooneGroupModularMachine` formalizes Simpson's Definition 3 and
proves exactly the three facts the Aanderaa--Cohen group construction uses:

* `ModularMachine.halts_iff_of_step` -- one step does not change whether a
  configuration halts.  This is the determinism/termination fact that makes
  the halting set a *good* subgroup in the sense of Simpson's Definition 2,
  and it is used nowhere else;
* `ModularMachine.haltsZ_right_iff` and `haltsZ_left_iff` -- the same fact
  transported to the index set `Z x Z` on which the free basis of the base
  group is indexed, in the parametrised form
  `(a + uM, b + vM) |-> (c + uM^2, v)` respectively
  `(a + uM, b + vM) |-> (u, c + vM^2)` in which the HNN associated
  isomorphisms act on basis indices.

## A repair to the source, and why it costs nothing

Simpson's Definition 3 does not require the halting configuration `(0,0)` to
be terminal.  Without that, `halts_iff_of_step` is *false* in the forward
direction: if some quadruple begins at `(0,0)` then `(0,0)` halts but its
successor need not, and the good-subgroup argument for `T_M` breaks.  The
field `quad_zero_zero` supplies the missing requirement.  It costs nothing:
in the Turing-machine simulation behind
[[modular-machine-with-noncomputable-halting]] the configuration `(0,0)` is
the halted one and carries no quadruple.

The bound `c < M^2` of Definition 3 is likewise load-bearing and is recorded
as `quad_lt`: it is what forces a *negative* parameter `u` to be sent to a
*negative* first coordinate in `haltsZ_right_iff`, which is how the integer
index map restricts to a bijection of the nonnegative quadrant.

Determinism, by contrast, is definitional rather than a hypothesis: the
quadruples are packaged as a function `quad : N -> N -> Option (N x Bool)`, so
the source's "at most one quadruple beginning with `(a,b)`" holds by
construction and `step` is a partial function rather than a relation.

## Which proof of Novikov-Boone this commits the chain to

Not Boone 1954--57 streamlined by Britton, whose tower is four-stage over a
free group with associated subgroups given by a long list of words and whose
correctness is a multi-page case analysis.  The chain follows the **modular
machine** proof of Aanderaa and Cohen (*Modular machines I, II*, in *Word
Problems II: The Oxford Book*, North-Holland 1980), in the written-out form of
Simpson's 2005 note: base group `<t, x, y | xy = yx>`, one family of stable
letters (one per quadruple, all with the same shape of associated subgroup),
then one further stable letter `k`, and correctness in three short lemmas.
Every declaration in the chain is named after the numbered item of that note
it formalizes, so the correspondence is checkable line by line.
