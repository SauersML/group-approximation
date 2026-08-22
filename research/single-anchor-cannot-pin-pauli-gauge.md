---
rg: 2
id: single-anchor-cannot-pin-pauli-gauge
kind: claim
title: One observable cannot pin a Pauli factor, while code columns pin it uniformly
distinct_from:
  generator-column-pauli-test-globalizes-but-does-not-pin-sites: that exhibits the global conjugacy left by the unanchored test; this characterizes exactly what an anchor packet must generate and proves the code-column adjoint estimate.
  kazhdan-and-transverse-packets-cannot-orient-clifford-twist: that leaves a spectator sign in a Clifford implementer; this first proves the one-observable impossibility and then separates genuine Pauli-column anchors from twisted normalizer words.
  quantum-expander-relative-commutant-rounding: that assumes a random-unitary expander of the form `C_j tensor I`; this proves that the generator columns satisfy such an estimate and records why ordinary normalizer words need not.
---

Put

```text
A=M_(2^n)(C) tensor I_K <= M_(2^n)(C) tensor M_K(C).
```

No single unitary or self-adjoint external observable `T` can have the
property

```text
WTW^*=T  implies  W in A'.                                (SAP1)
```

For a unitary `T`, take `W=T`; `(SAP1)` would first force `T in A'`.
Then every unitary in `A` commutes with `T`, so `(SAP1)` would force
`A subseteq A'`, impossible for `n>0`.  For self-adjoint `T`, use all
`W=exp(isT)` and the same argument.  Thus coupling the recovered Pauli
factor to **one** mark/computation observable cannot pin its global gauge,
even in exact finite dimension.

More generally, a finite anchor family `F` has harmless stabilizer exactly
when

```text
F'=A',                  equivalently W*(F)=A.             (SAP2)
```

The equivalence is the finite-dimensional bicommutant theorem.  Its robust
version is exactly an adjoint Poincare inequality for `F`.

The corrected de la Salle generator columns give such an inequality without
any dimension loss.  Let `S_X,S_Z subset F_2^n` be spanning column multisets
whose uniform measures have inverse spectral-gap constants `c,c'`.  On the
exact Pauli factor write `X(s),Z(t)`.  For every
`Y in A tensor M_K`,

```text
||Y-E_(A')(Y)||_2^2
 <= max(c,c')/2 * (
      E_(s in S_X)||[Y,X(s)]||_2^2
     +E_(t in S_Z)||[Y,Z(t)]||_2^2).                     (SAP3)
```

Indeed expand `Y` in the orthonormal Pauli basis.  The coefficient indexed
by `(a,b)!=(0,0)` pays at least `2/c` under the `X` conjugations when
`b!=0`, and at least `2/c'` under the `Z` conjugations when `a!=0`.
The `(0,0)` coefficient is precisely `E_(A')(Y)`.

This anchor size is optimal among Pauli-word anchors up to constants.  If
`q<2n` Pauli words are used, their symplectic labels span a proper subspace
of `F_2^(2n)`.  A nonzero label in its symplectic orthogonal gives a Pauli
word commuting with every anchor but not belonging to `A'`.  Hence a fixed
number of Pauli anchor words can never satisfy `(SAP2)` as `n` grows; the
`Theta(n)` columns of two asymptotically good codes are the correct scale.

Abstract constant-degree quantum expanders can replace the linear-size
Pauli family, but only if the named anchors really act as `C_j tensor I_K`.
Ordinary Clifford-normalizer group relations allow `C_j tensor V_j`.
`normalizer-multiplicity-twist-breaks-prefix-expander-rounding` gives an
exact correlated spin--multiplicity fixed vector in that model, so a fixed
normalizer packet does not provide `(SAP3)` in arbitrary representations.

Consequently there are only two sound uses of anchors here:

1. expose the `Theta(n)` generator-column Pauli words with their sampled
   average and use `(SAP3)`; or
2. make the payload itself gauge-covariant, so no old-frame pinning is
   required.

The first option still needs bounded-area self-similar names for the dense
column Paulis.  A short random seed and a polynomial-time classical column
decoder do not provide those group words.

