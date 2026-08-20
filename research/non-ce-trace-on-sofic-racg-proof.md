---
rg: 2
id: non-ce-trace-on-sofic-racg-proof
kind: route
title: Pull the BCS trace through its context Coxeter cover
target: non-ce-trace-on-sofic-racg
requires:
  - mipstar-bcs-tracial-nonru-exists
  - paddock-slofstra-bcs-forbidden-projection-dictionary
---

The context commutation and involution relations are precisely the defining
relations of `W_*`, so the BCS quotient map gives `C*(W_*) -> A_(B_*)` and
pullback gives `tilde tau_*`.  If this pullback were Connes embeddable, its
matrix moments on the finitely many generators would give a Connes-embeddable
state of the quotient: the forbidden projections have trace zero, hence vanish
in the GNS representation, and the dictionary identifies the resulting state
with a perfect `R^U` strategy.  This contradicts the first prerequisite.

The standard geometric representation of a right-angled Coxeter group is a
faithful integral linear representation. Mal'cev residual finiteness for
finitely generated linear groups therefore makes `W_*` residually finite, and
residual finiteness implies soficity. Finally the dictionary writes each
forbidden atom as the displayed fixed product of commuting generator
involutions, proving the last clause.
