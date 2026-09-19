---
rg: 2
id: cmps-two-oracular-rstar-lift-has-commuting-context-stars
kind: claim
title: Lemma 20 yields an R-star perfect-gap family whose incident context algebras commute mutually
distinct_from:
  culf-mastel-rstar-fixed-language-gap-is-published: that specializes the generic Culf--Mastel source and retains only contextwise commutation; this starts from the stronger 2-oracularizable 3SAT-10 source and preserves radius-two commutation in a chosen completeness lift.
  commuting-neighborhood-pruning-pays-atom-mass: that is the abstract projection inequality once mutually commuting neighbor PVMs are given; this supplies those PVMs around every variable star in one fixed-language family.
  culf-mastel-rstar-halt-model-has-fano-cap-support: that asks for cap-valued positive supports; mutual commutation permits joint pruning but does not force a cap or remove a Fano line.
---

**ESTABLISHED BY CITATION AND AN EXACT COMPLETENESS LIFT.**  There is a
computable finite perfect-gap family over the single relation `R_*` such that
on every completeness instance one may choose a perfect strategy satisfying

```text
[A_x,A_y]=0
whenever x,z and y,z occur in two target contexts.        (TOR1)
```

Consequently, for every target variable `z`, the assignment-PVM algebras of
all `R_*` contexts incident to `z` commute mutually.  They have a joint PVM
and satisfy the load-bearing hypothesis of
`commuting-neighborhood-pruning-pays-atom-mass` on that star.

By `cmps-lemma20-is-radius-two-incidence-commutation`, the source is an
RE-hard perfect-versus-constant-gap family of `3SAT-10` clause-variable
games with binary observables satisfying

```text
[A_x,A_y]=0  if x,y lie in one source context,            (TOR2)
[A_x,A_y]=0  if x,z and y,z lie in two source contexts.   (TOR3)
```

Property `(TOR3)` is their `2`-oracularizability.  It is stronger than
ordinary game oracularizability, which imposes commutation only on question
pairs having positive sampling weight.

Apply the contextwise NP/pp reduction used in Culf--Mastel Corollary 6.7 and
Theorem 6.8 with fresh private auxiliaries for every source context.  On
completeness, choose one target witness for each satisfying source
assignment.  Every target observable in the gadget replacing source context
`i` is a signed sum of its joint source atoms, so it belongs to the
commutative source context algebra `D_i`.

If source contexts `i,j` share `z`, then `(TOR3)` implies that `D_i` and
`D_j` commute elementwise.  If a target variable is private, all its
incident constraints remain inside one `D_i`; if it is original, any two
incident gadgets come from source contexts sharing it.  Subdivision leaves
these exact observables unchanged.  Proposition 6.2 removes an empty binary
constraint by defining every new auxiliary as a function of the joint atoms
of its two commuting variables, so it also stays inside that constraint
algebra.  This proves `(TOR1)` in the final `R_*` strategy.

All templates have fixed size, and the weighted-algebra comparison maps in
Culf--Mastel preserve a constant soundness gap.  Thus the construction has
the required finite perfect-CE-versus-no-perfect-CE RE orientation.

This closes only the mutual-neighbor commutation part of the Fano route.
Joint pruning can leave the full seven-point `R_*` support unchanged, so no
Fano-cap support or affine-safety conclusion follows.
