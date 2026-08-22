---
rg: 2
id: non-hyperlinear-from-group-factor-bcs-model
kind: route
title: A group factor satisfying the tracial non-RU constraint system is non-Connes-embeddable, so its group is the witness
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - non-ru-bcs-is-satisfiable-in-a-group-factor
---

Let `B_*` be the constraint system supplied by
`mipstar-bcs-tracial-nonru-exists` and let `A(B_*) -> L(Lambda)` be the
unital *-homomorphism of `non-ru-bcs-is-satisfiable-in-a-group-factor`.
(into a corner `p L(Lambda) p`, with `p = 1` allowed).  Compose with the
normalised trace `tau_Lambda(p . p)/tau_Lambda(p)` to obtain a tracial state
`tau` on `A(B_*)`; the image generates `Q = pi_tau(A(B_*))'' subset p L(Lambda) p`
with the restricted trace.  If `Q` were Connes embeddable, the GNS map
`A(B_*) -> Q -> R^U` would be a unital *-homomorphism into a tracial matrix
ultraproduct, contradicting the non-`R^U`-satisfiability of `B_*`.  Hence
`Q`, with it `p L(Lambda) p`, and with it `L(Lambda)`, is not Connes
embeddable (Connes embeddability passes to von Neumann subalgebras and to
corners, and `L(Lambda)` embeds in `R^U` iff each of its corners does), and
`Lambda` is not hyperlinear (Radulescu: a group is hyperlinear iff its group factor is
Connes embeddable).

The witness is the host `Lambda`, which this route leaves entirely free;
it is explicit exactly to the extent that the model in the hole is.  The
route is the unrestricted form of `non-hyperlinear-from-algebraic-envelope`
and `nonhyperlinear-from-algebraic-compact-action-envelope`: those fix the
host to be an algebraic compact-abelian semidirect product and the model
to be an embedding of the IRS relation algebra; here any group factor and
any BCS model suffice.
