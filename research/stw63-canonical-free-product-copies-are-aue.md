---
rg: 2
id: stw63-canonical-free-product-copies-are-aue
kind: claim
title: The canonical Jiang--Su copies in the full unital free product are approximately unitarily equivalent
---

For `F=Z*_(C)Z`, the two canonical unital embeddings

```text
i_0,i_1:Z->F
```

are approximately unitarily equivalent.

This is an open claim equivalent to STW Problem LXIII by
`stw63-universal-free-product-test`.

## Attempts

The fold homomorphism `F->Z` identifies the two copies, so it cannot give a
lower bound on their unitary-orbit distance.  Their `KK`, K-theoretic,
tracial, ideal, and presently known Cuntz data also agree.

The exact remaining positive task is to prove that the scalar `Delta` in
`stw63-universal-free-product-test` vanishes.  A negative solution requires a
norm lower bound `Delta>0`; a lower bound visible only in a quotient cannot
work if the quotient pair is already approximately conjugate.

Passing to the tracial von Neumann completion does not furnish a lower bound,
because the two nuclear embeddings are approximately unitarily conjugate
there.  Any obstruction must therefore detect the failure to approximate the
factor implementing unitaries by unitaries of the full free-product
C\*-algebra itself.

That completion does give a sharp no-go for one stronger strategy.
`stw63-full-tracial-shadow-forbids-joint-z-bridge` uses triviality of the
central-sequence algebra of the reduced free-product factor to prove that the
canonical pair has no common unital `Z` in its joint relative commutant in
`F_infinity`.  This refutes the universal joint-bridge proposal but gives no
positive lower bound on `Delta`; the AUE claim here remains open.

There is also a direct orbit obstruction short of a norm gap.
`stw63-canonical-free-product-implementers-escape-weakly` proves that the two
copies are not exactly unitarily conjugate, even in the reduced free-product
factor, and that the image of every prospective approximate implementing
sequence converges ultraweakly to zero there.  Thus finite reduced-word or
weakly precompact conjugator ansatzes cannot work.  Zero lies in the
ultraweak closure of the unitary group, however, and the factor itself has
implementing sequences with precisely this escape behavior, so this does not
decide whether `Delta=0` in `F`.
