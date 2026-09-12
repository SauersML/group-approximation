# STW Problem XII: outer-periodic-action AF-embedding audit

## Theorem

If `A` embeds into an AF algebra and `alpha^n=Ad(v)` for a multiplier unitary
`v`, then

```text
A rtimes_alpha Z
```

embeds into an AF algebra.  The proof first embeds the crossed product into
`M_n(A tensor C(T))` using a cyclic block shift whose wrap-around entry is
`vz`, where `z` is the circle coordinate, and then embeds that matrix circle
algebra into AF.

Since every separable AH algebra is AF-embeddable, this proves Problem XII
whenever the automorphism has finite order in `Out(A)`.  Real rank zero and
prior quasidiagonality of the crossed product are unnecessary in this slice.

## Faithfulness audit

Covariance alone would not show that the integrated representation is
injective.  The wrap-around variable is essential.  Rotating it by
`lambda^n` and conjugating the matrix coordinates by

```text
diag(1,lambda,...,lambda^(n-1))
```

sends the cyclic implementer to `lambda` times itself while fixing the
coefficient algebra.  Averaging this genuine target gauge action recovers
the canonical faithful expectation.  This proves injectivity for the full
C*-completion, not merely for finite Fourier polynomials.

For nonunital `A`, both `v` and the cyclic shift are multipliers, but
coefficient-times-shift monomials lie in `M_n(A tensor C(T))`; hence the
integrated crossed product still lands in the algebra rather than only its
multiplier.

## AF-target audit

An AF embedding of `A` and the pullback embedding
`C(T)->C(Cantor)` tensor to an embedding into the tensor product of two AF
algebras.  Matrix amplification stays AF.  No extension theorem, UCT,
quasidiagonality-to-AF implication, trace classification, or real-rank
argument is used.

The AH input is the standard theorem stated explicitly in Rordam,
*A purely infinite AH-algebra and an application to AF-embeddability*,
Israel J. Math. 141 (2004), arXiv:math/0205292: every AH algebra is
AF-embeddable.  The broader primary comparison is Huaxin Lin,
*AF-embedding of crossed products of AH-algebras by Z and asymptotic
AF-embedding*, arXiv:math/0612529, which proves other large classes using
K-theory and invariant traces.  Searches of the current Cairn graph and the
primary catalogue found no existing node with the elementary periodic
Floquet theorem above.

## Limitation

The argument requires the exact relation `alpha^n=Ad(v)`.  It does not cover
approximately inner powers, approximately periodic actions, finite-order
maps on K-theory, or general quasidiagonal crossed products.  Therefore it
is a genuine positive subclass, not a solution of Problem XII.
