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

## Proof

The coefficient of `Z(b)` from the `x` block to the `x+b` block is

```text
A_(x,b)=R_(x+b)R_x^*.                                        (MP5)
```

The identity commutator compares `A_(x,b)` with `A_(x+b,b)=A_(x,b)^*`.
Hence `(MP2)` says every quotient `R_yR_x^*` is self-adjoint.  Fix an anchor
`x_0`, set `G=R_(x_0)`, and `S_x=R_xG^*`.  Taking `y=x_0` shows `S_x=S_x^*`.
For arbitrary `x,y`, self-adjointness of `R_yR_x^*=S_yS_x` now gives
`S_yS_x=S_xS_y`.  This proves `(MP3)`.

Simultaneously diagonalize the commuting reflections.  On each joint
eigenline, write `S_x=(-1)^P(x)` for a Boolean function `P`.  Both sides of
`(MP4)` are the trace-weighted sums of their scalar counterparts, so `(PT6)`
from `phased-translations-reduce-to-alpha-plane-test` proves `(MP4)`.

## Sharp boundary

This argument does **not** robustly round a merely approximate identity
matching by itself.  A large family of Pauli reflections can realize any
prescribed sparse anticommutation graph.  Taking sparse graphs with vanishing
edge density but no large independent set makes the average pairwise
commutator energy tend to zero while preventing approximation of most
reflections by one commuting family.  Therefore a dimension-free proof with
both matchings approximate must exploit the alpha-plane relation jointly; an
"approximately commute, then diagonalize" step is not a valid standalone
reduction.

