# Boone--Higman: the covering kernel controls the remaining coset repair

## What is new

After restoring the distinction between a finitely presented marked cover
Gamma and its elementary image Q, an unexamined possibility remained:
a proper quotient Gamma/M might no longer map to a nontrivial quotient of Q.

The canonical proof ck-cover-quotient-kernel-dichotomy-proof gives the
exact alternative. Put K=ker(Gamma->Q). If the inherited simple core has
finite bi-index in Gamma/M, then

    image(M in Q)=Q,     Gamma=MK,     Gamma/M ~= K/(K intersect M).

Thus this kind of repair must obtain the entire new group from the
covering kernel. Merely changing the quotient while leaving a nontrivial
matrix quotient available cannot work.

This is a necessary condition, not a construction. It does not exclude
the existence of a finitely presented simple quotient of the cover whose
simple core has infinite bi-index, since such a quotient would already
solve the embedding problem without the coset criterion.

## Why maximal quotients split into two cases

For maximal proper normal M, normality and maximality give MK=M or
MK=Gamma. In the first case M contains K and the simple quotient descends
to Q. In the second case K surjects onto the simple quotient and M maps
onto Q. This is the precise missing distinction in any attempt to assign
a proper matrix level to every maximal kernel upstairs.

If K were proved solvable or locally finite, the second case would be
excluded: its quotients cannot be a finitely generated group containing
the infinite perfect simple core. Under either hypothesis all maximal
simple quotients descend to Q, and no proper quotient repairs the
canonical finite-bi-index action.

No such structural property of the actual covering kernel is claimed.
In particular, replacing an unknown unstable Steinberg kernel by the
stable abelian K_2 would be an additional unjustified step.

## Relation to finite presentation

The corrected construction has finitely presented Gamma, so the desired
simple quotient is finitely presented precisely when M is finitely
normally generated in Gamma. The dichotomy proves no such finite
generation. When K surjects onto that quotient, its kernel K intersect M
also need not inherit finite-generation properties from M.

When M contains K, the quotient is a matrix quotient, but finite
presentation of Q is still unavailable. The finite-presentation
criterion must be applied upstairs to Gamma, rather than transferred to
Q without proof.

## Research consequence

The canonical coset lane now has a sharper condition to test: a successful
quotient escaping the matrix obstruction must be a suitable quotient of
the covering kernel. Neither this quotient nor its required finite
presentation has been produced. The maximal-simple-quotient lane and the
projective-host lane remain open.

This is an algebraic proof recorded in Cairn, not a GPU experiment or a
Lean-verified theorem. Structural graph validation checks its wiring and
status, not the mathematical argument itself.
