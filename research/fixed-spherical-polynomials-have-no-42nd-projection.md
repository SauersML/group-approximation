---
rg: 2
id: fixed-spherical-polynomials-have-no-42nd-projection
kind: claim
title: No fixed spherical Hecke polynomial is a trace-one-over-forty-two projection
distinct_from:
  finite-spherical-moments-do-not-fold-regular-double: That gives atomic quadratures for arbitrary finite moment lists; this proves the sharper exact obstruction to naming the desired projection by one fixed spectral polynomial.
  sl3-one-over-forty-two-packet-is-external-or-folded: That rules out exact finite packet atoms; this rules out the first non-finite replacement, a fixed polynomial in the regular spherical Hecke operators.
  native-hecke-edge-rank-integrality-is-bounded: That bounds ranks in exact finite Hecke modules; this uses connectedness of the regular spherical spectrum and applies before any finite-module decomposition.
---

# No fixed spherical polynomial gives the forty-two-shell atom

Put

```text
G=SL_3(Q_2),       K=SL_3(Z_2),
H=C_c(K backslash G/K).                                 (FSP1)
```

Let `C_r^*(H)` be the closure of the spherical Hecke algebra in its regular
action on `l^2(G/K)`.  The Satake--Plancherel transform identifies this
commutative algebra with `C(X)`, where the reduced unramified spectrum `X` is
the compact tempered Satake torus modulo the finite Weyl group.  In
particular `X` is connected, and spherical Plancherel measure `mu_Pl` has
full support on `X`.  This is the rank-two instance of the standard reduced
spherical `C^*`-algebra description; see, for example, [R. Plymen, *Reduced
C*-algebra of the p-adic group GL(n), II*](https://arxiv.org/abs/math/0110018)
and the classical Satake transform.

Let `T_1,...,T_r` be any finite self-adjoint Hecke generators and let `f` be
one fixed self-adjoint noncommutative polynomial (commutativity makes its
transform an ordinary continuous function on `X`).  If

```text
q=f(T_1,...,T_r)                                        (FSP2)
```

is a projection in the regular spherical algebra, then

```text
f(x)^2=f(x)                  (x in X).                  (FSP3)
```

Connectedness forces the continuous `{0,1}`-valued function `f` to be
constant.  Hence

```text
tau_Pl(q) in {0,1},                                     (FSP4)
```

and never `1/42`.

There is also a microstate form requiring no operator-norm convergence.  If
a canonical regular-character matrix sequence evaluates the same fixed
polynomial and

```text
||q_n^2-q_n||_2 ->0,       ||q_n-q_n^*||_2->0,          (FSP5)
```

then finite-word moment convergence gives

```text
integral_X |f^2-f|^2 d mu_Pl=0.                         (FSP6)
```

Full support and continuity imply `(FSP3)`, so the limiting trace is again
zero or one.  Thus no fixed finite-depth spectral polynomial can produce an
asymptotic projection of trace `1/42` in canonical microstates.

The regular spherical von Neumann algebra is diffuse and does contain Borel
spectral projections of trace `1/42`.  The theorem says exactly why they do
not solve the presentation gate: such an indicator is discontinuous/algebraic-
infinite and cannot be named by one fixed Hecke polynomial.  Polynomial
approximants must have depth tending to infinity.  Their growing word and
coefficient complexity is not controlled by a fixed presentation defect.

Finally, finitely many moments cannot authenticate the Borel cutoff instead.
`finite-spherical-moments-do-not-fold-regular-double` replaces every such
finite list by an atomic quadrature while retaining the nonfolded value
`43/168`.  A conductor-dependent trace-`1/42` source must therefore use an
unbounded spectral filtration together with a new uniform section-defect
estimate; neither one fixed polynomial nor its finite moment table suffices.

Growth of the polynomial depth is not itself that estimate.
`single-denominator-borel-cuts-have-a-rohlin-escape` shows that any one
aperiodic denominator automorphism of a diffuse invariant conductor algebra
has trace-`1/42` Rohlin cuts with vanishing covariance defect.  Polynomial
approximants may be chosen along a diagonal slow enough to absorb arbitrary
finite propagation constants.  The surviving obstruction must deny such an
invariant algebra or use a jointly gapped family of denominator charts.
