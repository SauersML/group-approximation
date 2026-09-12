---
rg: 2
id: sl3-atomic-ambient-is-absorbed-by-lattice
kind: claim
title: Every amenable atomic model of the S-arithmetic SL3 group is absorbed by the integral lattice algebra
distinct_from:
  sl3-overlap-full-in-fd-ambient-images: that proves equality of the overlap, lattice and ambient images in each finite-dimensional representation; this uses summability of the atomic trace weights to pass from simultaneous equality on every finite family of blocks to equality of the generated von Neumann algebras in an infinite atomic model.
---

Fix a prime `p` and put

```text
C=SL_3(Z),                    A=SL_3(Z[1/p]).
```

Let `pi:A->U(N)` be any homomorphism into a finite tracial von Neumann
algebra and suppose

```text
Q=pi(A)''
```

is amenable.  Then

```text
pi(C)'' = pi(A)''.                                      (AA1)
```

In particular `(AA1)` holds for every homomorphism `pi:A->U(R)` into the
hyperfinite `II_1` factor.  Hence, with `P=pi(C)''`,

```text
E_P(pi(g))=pi(g),              ||E_P(pi(g))||=1          (AA2)
```

for every `g in A`, including every `g notin C`.  No injective or
noninjective model in `R` can satisfy the exteriority condition `(EXT)` of
`sl3-pair-admits-exterior-atomic-model`.

The point is joint finite-block matching.  Property `(T)` makes `Q` atomic,
so its faithful trace is a summable weighted direct sum of
finite-dimensional irreducible ambient representations.  The established
finite-dimensional overlap theorem applies to the direct sum of any finite
family of these blocks, producing **one** lattice element which matches a
given ambient element on all selected blocks simultaneously.  Exhausting
the summable weights puts that ambient unitary in the `L2` closure, hence the
von Neumann closure, of `pi(C)`.

Thus the proposed noncanonical amenable-edge escape is unavailable for the
arithmetic pair as well as for strict compressed pairs.  Any positive model
of the arithmetic doubles or centralizer HNN must use a nonamenable lattice
algebra; Brown--Dykema--Jung amenable-base permanence cannot originate it.
