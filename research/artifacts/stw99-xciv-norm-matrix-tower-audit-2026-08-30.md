# STW Problem XCIV: norm-matrix-tower audit (2026-08-30)

## Source definition and open root

Schafhauser--Tikuisis--White define separable `D`-stability to mean that every
norm-separable subset of the ambient algebra is contained in a norm-separable
`D`-stable subalgebra; see footnote 21 of
[Nuclear C\*-algebras: 99 problems](https://arxiv.org/html/2506.10902v2).
At Problem XCIV they ask this for `D=Z` and the hyperfinite II1 factor `R`, and
state that a suitably large-relative-ultrapower version of property (SI) would
give a positive answer.  The unrestricted question remains open here.

## Audit of the existing XCIV routes

All local XCIV claims and proof routes were checked before adding the matrix
tower theorem.  The existing positive subclass requires a unital CAR algebra
in the exact relative commutant of the whole seed.  The local-central
equivalence instead asks for actual operator-norm-central `Z` embeddings for
every finite subset of `R`.  The property-(SI) route remains conditional, and
the recorded orthogonal-corner example correctly shows why tracial
centrality alone cannot choose norm-central representatives.

The new class is not an instance of the exact-commutant theorem.  In a dyadic
model `R=(union_n M_(2^n))''`, the norm closure of the matrix union is the CAR
algebra and is weakly dense in `R`; consequently its relative commutant in
`R` is scalar.  Instead, the proof centralizes one finite matrix stage at a
time.  Its tail relative commutant is an infinite UHF algebra and contains a
unital `Z`, while operator-norm approximation of the prescribed finite set by
that stage converts exact stage commutation into small norm commutators.

## Exact boundary

The hypothesis is one coherent increasing tower of full matrix algebras with
operator-norm distance tending to zero.  Replacing that distance by tracial
`2`-norm distance would make the approximation available throughout `R` but
would invalidate the commutator estimate: the bound used in the proof is

```text
||[x,phi(z)]|| <= 2 ||x-b|| ||z||.
```

Thus the theorem proves separable `Z`-stability for every subset lying in a
UHF norm core of `R`, including a weakly dense core, but makes no assertion
for an arbitrary norm-separable subset of `R`.
