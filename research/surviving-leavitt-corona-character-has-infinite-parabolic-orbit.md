---
rg: 2
id: surviving-leavitt-corona-character-has-infinite-parabolic-orbit
kind: claim
title: A surviving Leavitt corona character atom has an infinite parabolic orbit
distinct_from:
  norm-corona-sparse-global-character-atom: that selects a nonzero global character projection for a countable root module; this proves that every nontrivial such atom is moved through infinitely many orthogonal character projections by the opposite parabolic vertex.
  maximal-sparse-character-atom-does-not-return-multiplicity: that audits coordinatewise maximal ranks under one branch return; this gives an exact representation-level obstruction to every finite orbit closure, with no rank comparison.
  ordinary-leavitt-parabolic-atomic-spectrum-is-trivial: that uses positive trace to make every orbit of a von Neumann atom finite and then kills the whole atomic summand; this works for a possibly rank-one norm-corona atom and concludes instead that its orbit must be infinite.
artifacts:
  - research/surviving-leavitt-corona-character-orbit-proof.md
---

Let `L=L_(F_2)(1,2)`, let `n>=4`, and let

```text
rho:St_n(L)->U(Q)
```

be a unitary representation in any unital algebra `Q`.  Put

```text
N=<x_(i n)(a):1<=i<n, a in L>~=(L,+)^(n-1),
H=St_(n-1)(L),
```

where `H` is the upper-left vertex and normalizes `N`.  Suppose a nonzero
projection `P` and a character `chi:N->{+1,-1}` satisfy

```text
rho(v)P=chi(v)P                         for every v in N.   (PCO1)
```

If `chi` is nontrivial, then the conjugacy orbit

```text
{rho(h)P rho(h)^(-1):h in H}                              (PCO2)
```

is infinite.  Distinct members of the corresponding character orbit are
pairwise orthogonal projections.  In particular, when `Q` is a norm matrix
corona and `P` is the sparse global atom selected from a surviving marked
last-column root, no finite parabolic packet can close around `P`.

Indeed, a finite orbit would give a homomorphism from `H` to a finite
permutation group.  Every finite-dimensional unitary representation of the
binary-Leavitt Steinberg cover is trivial, so this permutation action is
trivial.  Hence `P` is fixed by `H` and `chi` is `H`-invariant.  Upper-left
elementary transvections add arbitrary multiples of one last-column
coordinate to another.  Character invariance under all of them forces every
coordinate character to be trivial, contradicting the hypothesis.

This is exactly where positive trace was used in the tracial atomic theorem
and is unavailable here.  In a finite tracial algebra, infinitely many
orthogonal conjugates of one positive-trace atom are impossible.  A norm
matrix corona can contain infinitely many mutually orthogonal equivalent
sparse projections: at each fixed finite stage only finitely many are
visible, while their number grows with the coordinate.  Thus `(PCO2)` does
not itself collapse the mark.  It proves that a successful corona decoder
must fold an intrinsically infinite parabolic character orbit back to one
finite projective reservoir; finite atom cycles, bounded character menus,
and finite parabolic closure are ruled out.

DERIVATION
surviving-leavitt-corona-character-orbit-proof
