# Sofic halo permanence as a Clifford-tape falsification test

Source: Alekseev--Bradford, arXiv:2601.18742v1,
*Sofic actions, halo products, and metric approximations of groups*.

The paper defines a sofic `C`-action of a group on another group by
automorphisms.  Its main technical theorem applies to any metric family that
is product-compatible and wreath-compatible.  Corollary `BigSemiCoroll`
specializes it to sofic, linear-sofic, hyperlinear and weakly sofic groups:
if `Gamma` and `Delta` lie in the chosen class and the action is a sofic
`C`-action, then `Delta semidirect Gamma` lies in the same class.

For set- or graph-theoretic haloes, their Proposition
`SoficActSoficAutoProp` shows that a sofic action on the underlying sites
induces the required sofic action by automorphisms whenever every finite halo
group lies in `C`.  Hence the corresponding halo product is hyperlinear when
the finite halo pieces and acting group are hyperlinear.  The paper includes
restricted wreath products, graph wreath products, symmetric enrichments and
many related many-site constructions in this framework.

This is a sharp no-go theorem for a naive reading of “copy the bad region and
move it everywhere.”  If the Clifford tape is merely a functorial family of
finite Pauli lamps over a sofic site action, its semidirect/halo product is
hyperlinear.  Adding a high-distance code to the local lamp alphabet does not
change this conclusion when finite code blocks remain uniformly within the
hyperlinear halo class.

Therefore a successful fault-tolerant Clifford tape must exhibit a concrete
escape from the permanence theorem.  Plausible escape points are:

- the action on packet coefficients is not a sofic `C`-action;
- the return is a genuinely two-dimensional quotient/holonomy, not a
  semidirect halo product;
- the code constraints couple sites in a nonfunctorial way that cannot be
  recovered from finite induced substructures;
- or the same-model trigger introduces a quotient relation after the halo
  construction, and that quotient is exactly where approximability fails.

Merely asserting “self-similarity” is not an escape: regular shifts and many
equivariant enrichments are among the approximable cases covered by the
paper.
