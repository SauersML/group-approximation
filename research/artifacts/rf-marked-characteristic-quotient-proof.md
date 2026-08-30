# Marked characteristic quotients of finitely generated RF groups

## Statement

If a finitely generated residually finite group `Gamma` contains `1!=y`, then
there is a finite-index characteristic subgroup `C` not containing `y`.
Thus every automorphism action on `Gamma` descends simultaneously to the one
finite marked quotient `Gamma/C`.

## Bounded-index finiteness

Fix a generating set of size `d`.  For a positive integer `k`, every subgroup
`H<=Gamma` of index `k` gives the transitive coset action on `Gamma/H`.  Choose
a bijection `Gamma/H -> {1,...,k}` sending `H` to `1`.  The resulting action is
a homomorphism

```text
rho_H:Gamma -> Sym(k)
```

and `H=rho_H^(-1)(Stab(1))`.  There are at most `(k!)^d` homomorphisms from
`Gamma` to `Sym(k)`, since the images of the `d` generators determine a
homomorphism.  Hence there are finitely many index-`k` subgroups, and therefore
finitely many subgroups of index at most any fixed `m`.

## The characteristic core

Residual finiteness gives a homomorphism from `Gamma` to a finite group which
does not kill `y`.  Its kernel `N` has finite index `m` and omits `y`.  Define

```text
C_m = intersection_[Gamma:H]<=m H.
```

The preceding section makes this a finite intersection.  It has finite index,
and it is contained in `N` because `N` occurs among the intersectands.  Thus
`y` is not in `C_m`.

For every automorphism `beta` of `Gamma`, the map `H |-> beta(H)` is a
permutation of the subgroups of index at most `m`.  Applying `beta` to the
intersection therefore gives `beta(C_m)=C_m`.  In particular `C_m` is
characteristic (and hence normal), so `Q=Gamma/C_m` is a finite group and the
image of `y` in `Q` is nonidentity.

## Simultaneous descent and the type orbit

Given `alpha:B->Aut(Gamma)`, define

```text
bar alpha(b)(g C_m)=alpha(b)(g) C_m.
```

Characteristicity makes this independent of the representative, and the
inverse is induced by `alpha(b^(-1))`; hence `bar alpha:B->Aut(Q)` is a
homomorphism.  Both `Q` and `Aut(Q)` are finite, so
`Q semidirect image(bar alpha)` is finite.  The natural semidirect-product map
from `Gamma semidirect B` sends `(y,1)` to a nonidentity element.

For the representation formulation, decompose the faithful regular
representation of `Q` into irreducibles.  If every constituent killed the
nonidentity element `q(y)`, their direct sum would kill it, contradicting
faithfulness.  Some irreducible therefore detects `q(y)`.  Pulling it back to
`Gamma`, its entire `B`-orbit factors through the finite group `Q` and is
contained in the finite set of irreducible representations of `Q`.
