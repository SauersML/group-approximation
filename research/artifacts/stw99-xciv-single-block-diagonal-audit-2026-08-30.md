# STW Problem XCIV: single-block commuting-column audit

## New reduction

Fix `D=I_(2,3)`.  Local operator-norm central copies of this one block are
equivalent to separable `Z`-stability of an arbitrary unital ambient algebra.
The forward implication follows by composing local central `Z` copies with a
fixed unital embedding `D->Z`.

For the reverse implication, a one-column diagonal would give only a central
copy of `D`, which is not enough for `Z`-absorption.  The construction uses a
triangular array of local maps.  At coordinate `n`, it creates `n` copies of
`D`, each chosen norm-central relative to the seed tests and the earlier
copies in that row.  Fixed columns then induce countably many pairwise
commuting homomorphisms

```text
D -> C_infinity intersect C'.
```

Nuclearity of `D` combines them into a unital homomorphism from
`D^(tensor infinity)`.

Dadarlat--Toms, Adv. Math. 220 (2009), Theorem 1.1,
arXiv:0707.4050, proves that the infinite tensor power of a unital separable
algebra is `Z`-stable when it contains unitally a subhomogeneous algebra
without characters.  The first tensor factor `D` supplies exactly that
hypothesis.  Thus `D^(tensor infinity)` contains a unital copy of `Z`, and
the commuting-column map produces the central `Z` embedding needed for the
hull.

## Strict norm boundary

All row-commutators tend to zero in operator norm.  This is used twice:

1. each column lands in the norm sequence relative commutant;
2. distinct columns commute there, so their multiplication represents the
   minimal tensor product.

McDuff `2`-norm tails give only the analogous statements in the tracial
sequence quotient.  The orthogonal Pauli-corner construction in
`stw99-xciv-two-norm-centrality-does-not-control-norm-centrality` shows that
one cannot select norm-central representatives from that information.
Therefore the single-block reduction simplifies the domain test but does
not weaken the topology required by XCIV.

## Consequence for XCIV

A negative answer is witnessed by one finite subset of `R`, one positive
commutator gap, and the fixed block `I_(2,3)`.  The earlier criterion allowed
the obstructing block size to vary; the commuting-column diagonal removes
that quantifier entirely.  No claim is made that such a gap exists.
