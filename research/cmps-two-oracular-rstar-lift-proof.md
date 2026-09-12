---
rg: 2
id: cmps-two-oracular-rstar-lift-proof
kind: route
title: Lift every private gadget coordinate inside its 2-oracular source context algebra
target: cmps-two-oracular-rstar-lift-has-commuting-context-stars
requires:
  - cmps-lemma20-is-radius-two-incidence-commutation
  - commuting-neighborhood-pruning-pays-atom-mass
  - culf-mastel-rstar-fixed-language-gap-is-published
---

Lemma 20 states `(TOR2)--(TOR3)` verbatim.  Its proof duplicates each old
variable locally, joins each local copy to the global variable by two
clauses, and assigns the same observable to both.  The paper then uses
`(TOR3)` when two smooth-label-cover questions have one possible common
partner.  Thus the quantifier is the whole radius-two incidence relation,
not only sampled edges.

For the fixed-language lift, let `P_(i,phi)` be the joint atoms of source
context `i`, and fix a classical witness section `s_i:C_i -> D_i` for its
private pp gadget.  For a target coordinate `t in W_i`, put

```text
B_t=sum_(phi in C_i) (-1)^(s_i(phi)(t)) P_(i,phi).        (TOR4)
```

These observables realize the target gadget exactly and lie in `D_i`.  On
an original coordinate the section extends `phi`, so `(TOR4)` is the old
`A_t` and different gadgets agree on overlaps.

If `i,j` contain a common source variable `z`, every generator of `D_i`
commutes with every generator of `D_j` by `(TOR3)`.  Products and linear
combinations therefore give

```text
[D_i,D_j]=0.                                              (TOR5)
```

Now fix a final target variable.  A private variable occurs only inside one
source gadget.  An original variable can occur in several gadgets, but
their source contexts all contain that variable and `(TOR5)` applies to
each pair.  Hence every generator in the union of its incident context
algebras commutes, producing the common joint refinement required for Fano
neighborhood pruning.

Culf--Mastel Corollary 6.7 supplies the private-variable extension,
Theorem 5.2 supplies bounded subdivision, and Proposition 6.2 explicitly
maps each new auxiliary for an empty pair constraint to a spectral function
of that pair.  Their comparison constants are uniform for fixed templates.
None of these maps restricts positive target support to a Fano cap.
