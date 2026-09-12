---
rg: 2
id: cyclic-energy-reverse-kleene-ceiling-diagonal
kind: claim
title: Reverse Kleene derives a strict finite-dimensional cyclic-energy ceiling without a stability modulus
distinct_from:
  cyclic-carrier-energy-stability: that assumes one fixed group already has a strict exact finite-dimensional ceiling and upper semicontinuity over all small-defect tuples; this derives the ceiling at a self-referential index and asks for upper semicontinuity only along canonical-profile microstates.
  threshold-free-reverse-kleene-higman-diagonal: that semidecides triviality of a marked word in a recursively enumerable presentation; this semidecides excess energy of an exact finite-dimensional representation and therefore uses a finite presentation, or an explicit excess recognizer.
  canonical-profile-kleene-higman: that compares a nonzero rational group-algebra mark with its canonical microstate norm; this compares a regular cyclic energy with the supremum of the same energy over exact finite-dimensional representations.
  kleene-mipco-self-destroying-game: that diagonalizes a commuting-operator game compiler against finite-dimensional game value; this is the group-presentation analogue for a trace-polynomial energy and concludes nonhyperlinearity.
---

Suppose a total computable compiler sends every Turing-machine index `e` to

- a finite group presentation `G_e=<X_e|R_e>`;
- a uniformly computable finite rational trace-polynomial energy `E_e(U)`
  (for example
  `sum_(s in S_e)||[U(s),f_e(U(w_e))]||_2^2` for rational trigonometric
  `f_e`);
- rational numbers `a_e>b_e`.

Put

```text
beta_e = sup{E_e(pi): pi is an exact finite-dimensional unitary
                         representation of G_e},
Ereg_e = E_e(lambda_(G_e)).
```

Assume

```text
e halts     => beta_e<=b_e,                               (EKT1)

e nonhalts  => Ereg_e>=a_e, and every canonical-profile
               microstate sequence U_n for G_e satisfies
               limsup_n E_e(U_n)<=beta_e.                 (EKT2)
```

Then one can effectively construct a finitely presented nonhyperlinear group.
The fixed-point program reads no relator-defect threshold, canonical-moment
tolerance, matrix-dimension bound, upper-semicontinuity modulus, convergence
rate, or runtime bound.

There is no hidden convergence theorem in the canonical clause of `(EKT2)`.
For a finite trace-polynomial energy, canonical moment convergence always
gives `E_e(U_n)->Ereg_e`. Hence that clause is logically equivalent to

```text
G_e is nonhyperlinear OR Ereg_e<=beta_e.                 (EKT2')
```

The compiler must prove the second disjunct from a hypothetical canonical
microstate; it may become vacuous precisely when the fixed-point group is
nonhyperlinear. An unconditional exact finite-dimensional excess witness
cannot replace this conditional implication, by
`cyclic-energy-excess-recognizer-is-essential`.

The same theorem holds for uniformly recursively enumerable presentations if
the compiler additionally supplies a uniform semidecision procedure for
`beta_e>b_e`. Such a procedure is automatic for finite presentations by exact
quantifier elimination over the reals, but is not automatic for a general
recursively enumerable relator stream.

This theorem is useful only for an asymmetric compiler satisfying
`(EKT1)--(EKT2)`. If one group is already known to have a strict exact ceiling
and the canonical upper bound, the direct canonical-moment contradiction
proves nonhyperlinearity and the fixed point adds nothing.
