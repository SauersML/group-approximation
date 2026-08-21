---
rg: 2
id: matrix-phased-translations-exact-identity-scalarize
kind: claim
title: Exact identity matching scalarizes every matrix-phased translation table
distinct_from:
  phased-translations-reduce-to-alpha-plane-test: that starts with scalar Boolean phases; this proves that arbitrary matrix block phases reduce to those scalar phases when the identity matching is exact.
  sampled-weyl-defect-controls-common-pvm-dirichlet-energy: that allows both sampled matchings to have error and arbitrary operator mixing; exactness of the identity matching is essential here.
---

ESTABLISHED.  Let `K=F_(2^n)`, let `E` be an arbitrary finite-dimensional
Hilbert space, and on `ell^2(K) tensor E` put

```text
X(a)=T_a tensor I,
R=sum_x |x><x| tensor R_x,          R_x in U(E),
Z(b)=R(T_b tensor I)R^*.                                      (MP1)
```

Thus `X` and `Z` are exact additive tables, with completely arbitrary matrix
phases `R_x`.  If the identity matching

```text
X(b)Z(b)=Z(b)X(b)                                             (MP2)
```

holds exactly for every `b`, then there is a unitary `G` and a commuting
family of self-adjoint unitaries `(S_x)` such that

```text
R_x=S_x G.                                                    (MP3)
```

Consequently the matrix phases simultaneously decompose into scalar Boolean
phases.  For a primitive `alpha`, even if the alpha matching is only
approximate, the complete commutator energy satisfies

```text
E_(a,b)||X(a)Z(b)-Z(b)X(a)||_2^2
 <=(27/2) E_b||X(alpha b)Z(b)-Z(b)X(alpha b)||_2^2.            (MP4)
```

The normalized trace may give the joint eigenspaces arbitrary multiplicity;
the constant is independent of `n`, `dim(E)`, and those multiplicities.

The proof is `matrix-phased-exact-identity-scalarization-proof`.

## Sharp boundary

This argument does **not** robustly round a merely approximate identity
matching by itself.  A large family of Pauli reflections can realize any
prescribed graph as its anticommutation graph.  Use, for example, a fixed-degree
regular graph on `N` vertices.  Its average pairwise commutator energy is
`O(1/N)`.  Yet if commuting unitaries `Q_i` approximate its Pauli reflections
`P_i`, every anticommuting edge obeys

```text
2=||[P_i,P_j]||_2 <=2(||P_i-Q_i||_2+||P_j-Q_j||_2).
```

Summing over the regular graph forces a constant average approximation error.
Therefore a dimension-free proof with both matchings approximate must exploit
the alpha-plane relation jointly; an "approximately commute, then diagonalize"
step is not a valid standalone reduction.
