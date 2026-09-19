---
rg: 2
id: erasure-cleaning-rounds-all-projective-parity-valleys
kind: claim
title: Robust Tanner erasure cleaning uniformly rounds every projective parity valley
distinct_from:
  central-clifford-parity-sectors-round-uniformly: that treats exact parity and uses code distance to charge every nonzero sign sector; this permits a vanishing set of failed original checks and identifies the geometric property needed to localize their cocycle freedom.
  bad-check-nullity-does-not-exclude-far-pauli-cocycles: that shows mere dimension loss under check deletion cannot localize projective cocycles; this proves that common-support erasure cleaning is sufficient.
  balanced-overlay-diffuse-square-function-newton: that concerns arbitrary noncentral diffuse tuples; this closes only the exact scalar-commutator/projective far-valley class.
---

Let `C=ker(H)<=F_2^L` have relative distance `delta`, bounded check width and
column degree, `M=Theta(L)` checks, and a linear classical soundness bound.
Assume the following robust erasure-cleaning property.  For every check set
`E` of size at most `eta_0 M`, there is a coordinate set `S(E)` with

```text
|S(E)| <= K (|E|/M)L,
ker(H_(checks outside E)) <= C + F_2^S(E).                (ECP1)
```

Consider reflections `Q_1,...,Q_L` whose pair commutators are scalar signs,
with alternating sign matrix `B`, and suppose every original parity word
outside a set `E` equals `I`.  Put

```text
eta=|E|/M,
beta=L^(-2)|{(i,j):B(i,j)=1}|.                           (ECP2)
```

For sufficiently small `eta`, there are commuting reflections `(Q_i')` on
the same Hilbert space, satisfying every parity check exactly, such that

```text
(1/L)sum_i ||Q_i-Q_i'||_2^2 <= C_1(eta+beta).             (ECP3)
```

The constants depend only on the code parameters and `(ECP1)`, not on
length, matrix dimension, or the projective sector.  The conclusion also
holds after central direct sums, with the right side averaged by central
trace weights.

Hence every asymptotic projective/Pauli far valley for the balanced overlay
forces failure of robust erasure cleaning.  Bott-type scalar cocycles,
finite-rank Clifford blocks, and quantum Tanner class-two strategies do not
give an additional obstruction once `(ECP1)` is available.  This does not
settle genuinely noncentral commutators, for which there is no binary sign
matrix `B` to clean.

