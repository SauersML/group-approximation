---
rg: 2
id: fp-upgrades-make-non-lef-and-non-lea-cheap
kind: claim
title: Finite presentation upgrades LEF and LEA to exact statements, which is why non-LEF and non-LEA are cheap and non-sofic is not
---

For a **finitely presented** group, two local approximation properties collapse
to exact ones:

* `fp` and LEF imply residual finiteness (Vershik--Gordon).  Hence
  `fp` and not residually finite gives **not LEF**, for free.
* `fp`, LEA and simple imply amenability.  Hence `fp`, simple and not amenable
  gives **not LEA**, for free.

Both are the same argument.  A local embedding of a finite window containing
the generators, every subword of every relator, and one nontrivial element
kills no relator, so it *is* a homomorphism on that window and factors through
the presented group; finiteness of the relator set is what makes the window
finite.  The target class then supplies the exact conclusion.

**No such upgrade is known for soficity or for MF**, and the reason is
structural rather than incidental: sofic and MF models are *approximate*
homomorphisms — almost-multiplicative maps into finite symmetric groups or
unitary groups — so a finite presentation does not turn a model into a genuine
homomorphism.  The relators are only approximately satisfied, and there is no
mechanism forcing the error to zero.

The empirical shape of the group property atlas is exactly this asymmetry.
Against nearly every companion property — CAT(0), biautomatic, type
`F_infinity`, finite cohomological dimension, decidable conjugacy problem,
Haagerup — a non-LEF and non-LEA witness is available immediately, because any
finitely presented infinite simple non-amenable group with that property serves
(Burger--Mozes supplies all six at once).  Against the same list, **not a single
non-sofic or non-MF witness is known**, and each cell is an open problem.

So the cost of a non-sofic example is not that soficity is a strong property;
it is that there is no finite-presentation lever on it.  Any route to the empty
cells either builds a new non-sofic group carrying the property directly, or
finds the missing lever — a hypothesis `P` for which `fp`, sofic and `P` force
an exact conclusion the way simplicity does for LEA.
