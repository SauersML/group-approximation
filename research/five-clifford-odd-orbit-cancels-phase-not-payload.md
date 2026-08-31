---
rg: 2
id: five-clifford-odd-orbit-cancels-phase-not-payload
kind: claim
title: The five-Clifford odd orbit cancels its spin phase but leaves an arbitrary multiplicity norm
artifacts:
  - research/five-clifford-odd-orbit-multiplicity-proof.md
distinct_from:
  extraspecial-fusion-filter-is-local-and-normalizer-globalization-is-matricial: that gives the general normalizer boundary; this audits the smallest five-generator Clifford orbit and supplies an exact finite hidden-sector representation.
  odd-tensor-closure-forces-a-threehot-hidden-sector: that concerns literal commuting selector spectra; here the local Clifford fusion filter is valid and the failure occurs in automorphism-extension multiplicity.
  finite-sheet-transport-networks-are-exactly-matricial: that treats coordinate-sheet permutations; here the hidden quotient action sits in the commutant of a unique spin representation.
---

Let
```text
K=<J,X_1,...,X_5 |
 J^2=X_i^2=1, J central, [X_i,X_j]=J (i!=j),
 X_1 X_2 X_3 X_4 X_5=J>.
```
Then `K` is extraspecial of order `32` and has a unique irreducible
`J=-1` representation `rho`, of dimension four.  Cyclic permutation
of the five `X_i` is an outer automorphism `alpha` of order five.
For
```text
L=K semidirect_alpha <g>,                 |g|=5,
```
`rho` extends to `L`, but every general marked representation has
the form
```text
pi(k)=rho(k) tensor I_M,
pi(g)=h tensor D,                         D^5=I_M.        (FCO1)
```
The factor `D` is unconstrained automorphism-extension multiplicity.

Adjoin an involution `V` centralizing `K`, put
`pi(V)=I_4 tensor A`, and set `U=X_1^a V`, `a in {0,1}`.  The
suggested odd-orbit extractor has the exact value
```text
pi(J^a) product_(i=0)^4 pi(g^i U g^-i)
 =I_4 tensor product_(i=0)^4 D^i A D^-i.                 (FCO2)
```
The Clifford relation cancels only the first tensor factor.  It does not
extract `A` from the second.

There is an exact finite countermodel: take `D` to be the regular
five-cycle on `C^5` and
```text
A=diag(-1,1,1,1,1).
```
Then the five conjugates in (FCO2) are all coordinate sign flips, hence
their product is `-I_5`, not `A`; their normalized Hilbert--Schmidt
distance is `4/sqrt(5)`.

No proper finite overgroup removes this uniformly while retaining only
the four-dimensional spin type.  If a finite `G>=K` with central `J`
had exactly one `J=-1` irreducible and it had dimension four, then
```text
|G|/2=dim p_- C[G]=16,
```
so `|G|=32` and `G=K`; but inner automorphisms of `K` cannot move
`X_1` to `X_i` modulo the center.  Proper outer extensions necessarily
supply quotient types or multiplicity sectors, and arbitrary
representations may use them.

A finer isotypic projection `q` can make `D` scalar and recover
`A^5=A` only when the payload reduces `q`.  Without reduction,
```text
(qxq)(qyq)-qxyq=-qx(1-q)yq.                              (FCO3)
```
Thus a genuinely nonnormal Hecke corner is not ruled out, but it must
control the off-corner leakage in (FCO3) by a dimension-free estimate.
The five-Clifford fusion and volume relations themselves give no such
control.  This is the exact surviving seam; phase cancellation alone is
not a decoder.
