# XCIII: ambient Powers averaging and the central commutator-lifting hinge

## Outcome

The realization

```text
D=(C*_r(F_2) tensor Z)_omega intersect (C*_r(F_2) tensor Z)'
```

has an intrinsic feature absent from the abstract doubled-`F(Z)` model:
every self-adjoint element of its trace-kernel ideal is a norm limit of
self-commutators in the full ultrapower.  Thus the full ultrapower has no
trace which detects the kernel.

Uniqueness of the ordinary trace on `D` is equivalent to the stronger
relative statement that the same elements are norm limits of
self-commutators whose factors lie in `D` itself.

## Coordinatewise Powers--Dixmier decomposition

The algebra `A=C*_r(F_2) tensor Z` is simple, exact, monotracial, Z-stable,
and has strict comparison.  Haagerup--Zsido gives the singleton Dixmier
property, and Archbold--Robert--Tikuisis upgrade it to uniform singleton
Dixmier averaging.  At each fixed tolerance, the number of averaging
unitaries is independent of the element.

For a positive trace-kernel representative `(h_n)`, choose coordinatewise
unitaries `u_(j,n)` such that

```text
m^(-1)sum_j u_(j,n)h_nu_(j,n)* ~= tau(h_n)1.
```

With `y_(j,n)=m^(-1/2)h_n^(1/2)u_(j,n)*`, the exact identity

```text
sum_j(y_(j,n)y_(j,n)*-y_(j,n)*y_(j,n))
 =h_n-m^(-1)sum_j u_(j,n)h_nu_(j,n)*
```

places the ultrapower class of `(h_n)` in the norm closure of ambient
self-commutators.

## Exact failure of central promotion

The averaging unitaries depend on the coordinate.  Norm-centrality of
`(h_n)` says nothing about commutators with this moving family.  Hence the
sequences `(y_(j,n))` need not be central, even though their self-commutator
sum is central.

Writing `Com_sa(C)` for the closed real span of self-commutators in `C`, the
exact remaining ordinary-trace statement is

```text
I_sa subset Com_sa(D).
```

The forward implication to unique trace follows because traces vanish on
self-commutators and `D/I` is a II_1 factor.  The reverse implication is
the Cuntz--Pedersen annihilator theorem: if `D` has one normalized trace,
all bounded tracial functionals are its scalar multiples, so the trace-zero
self-adjoint space is precisely `Com_sa(D)`.

This criterion is stronger than merely producing coordinatewise
commutators in `A`, and weaker than forcing every trace-kernel element to
belong to the Jiang--Su-saturated ideal.  It is the exact norm-level target
for any Powers averaging or free-factor spectral-gap attack.

## Source audit

- Archbold--Robert--Tikuisis, [*The Dixmier property and tracial states for
  C*-algebras*](https://arxiv.org/abs/1611.08263), establish uniform Dixmier
  averaging and its ultrapower permanence; their Theorem 3.2, Lemma 3.9,
  and Corollary 3.22 provide the form used here.
- Cuntz--Pedersen, *Equivalence and traces on C*-algebras*, Proposition 2.7,
  identifies the closed self-commutator space as the common kernel of
  bounded tracial functionals.

No claim is made that ambient averaging unitaries can be selected centrally.
That selection is precisely the remaining XCIII-specific hinge.
