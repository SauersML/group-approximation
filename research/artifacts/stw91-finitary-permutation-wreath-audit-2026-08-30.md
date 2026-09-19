# STW XCI: finitary permutation wreath audit

## Result

For a nontrivial countable linear group `P` with trivial amenable radical, a
countably infinite set `X`, and any subgroup `L <= Sym_fin(X)`, the group

```text
P^(X) rtimes L
```

has selfless reduced C*-algebra.  The theorem gives a whole semidirect class,
not merely a closure restatement: its proof constructs finite linear packets
and verifies their C*-simplicity hypothesis through an explicit amenable
radical calculation.

## C*-simplicity audit

The dangerous shortcut would be to say that a finite extension of a
C*-simple group is C*-simple.  The proof does not do this.  In a packet
`P^S rtimes K`, an amenable radical intersects `P^S` trivially and hence is
finite.  Its normality forces it to centralize `P^S`.  A nontrivial
permutation component cannot centralize a base element supported on a moved
coordinate, while a pure base component is already in the trivial
intersection.  Thus the packet radical is trivial.  Vigdorovich's theorem
then applies to that packet.

The condition `S contains supp(K)` is essential: it makes the finite
permutation action on the packet coordinates faithful.  It is preserved
when packets are enlarged, and every finite subset of the full wreath lies
in such a packet.

## Strict separation

The full group is not linear over any field.  Infinitely many commuting
nonabelian coordinate groups force a strictly increasing chain of unital
subalgebras in any hypothetical finite matrix algebra.  It is also not
acylindrically hyperbolic: every element has finite base and permutation
support, so its centralizer contains all coordinate groups off that finite
set and is not virtually cyclic.

Accordingly the example

```text
SL_3(Z)^(N) rtimes Sym_fin(N)
```

is outside the linear theorem at the level of the full group and outside the
acylindrically-hyperbolic (with or without rapid decay) route.  The theorem
makes no claim that the group fails every possible formulation of rapid
decay; no such claim is needed for the separation.

## Literature boundary

The primary-source comparison included Robert's directed-union theorem,
Vigdorovich's linear theorem (arXiv:2602.10616v3), Ozawa's PHP/extreme-boundary
theorem (arXiv:2508.07938), the 2026 selfless-correspondence crossed-product
paper (arXiv:2607.20361), the amalgamated-free-product/HNN theorem
(arXiv:2604.06982), and the 27 August 2026 almost-periodic crossed-product
preprint (arXiv:2608.26987).  The crossed-product theorems require PHP or a
topologically free extreme boundary for the acting group and hypotheses on a
simple coefficient algebra; they do not state the finitary permutation
wreath theorem above.  Searches for selfless finitary or permutational wreath
products found no primary-source theorem with this statement.

This is a new positive class for Problem XCI, not a solution of its universal
C*-simple-group assertion.
