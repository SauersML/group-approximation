---
rg: 2
id: kazhdan-projection-and-central-heights-force-external-mass
kind: route
title: Project a native central height into the canonical factor and compare its norm with Haar leakage
target: native-enlargements-require-external-haar-mass
requires:
  - native-s3-algebra-enlargement-obstructs-scalar-commutants
  - binary-leavitt-elementary-group-is-simple
  - binary-leavitt-unit-group-has-tt-mod-t
artifacts:
  - research/artifacts/leavitt-native-enlargement-external-haar-mass-2026-09-08.md
---

The native image `y_+=u k_+ u^(-1)` has infinitely many
distinct conjugates under `L`. Canonical trace and exact `L`
commutation imply `E_A(y_+)=0`. Since `y_+` lies in `uAu*`,
the reverse supremum leakage is exactly one.

The finite central-overlap calculation therefore gives, whenever
the forward Haar leakage is at most `1/4`, a self-adjoint central
contraction `z in A` with trace zero, squared norm at least `1/64`,
and squared commutator with `u` at most `2alpha/(1-exp(-1/16))`.
The calculation uses only the finite-dimensionality of `A` and
the ambient finite trace, so it applies inside any finite tracial
extension of the canonical group factor.

Exact `L` commutation and `S_3` capture make every other commutator
in the chosen finite generating set vanish. Conditional expectation
onto the native group factor preserves these identities. Its internal
conjugation Kazhdan gap bounds the squared norm of `E_N(z)` by
`2alpha/[kappa_H^2(1-exp(-1/16))]`.

The artifact proves directly that the squared distance of any
contraction in a finite algebra from a trace-preserving expectation
is at most twice its Haar-mean squared distance. Applying this to
`z` and subtracting its internal squared norm gives the external
Haar-mass bound. Setting that mass to zero proves the internal
obstruction, including the complementary case `alpha>1/4`.

For asymptotic capture and Haar `L`-centralization, the latter
gives uniform commutator control on each algebra's contraction ball.
Average any fixed number of the canonical orthogonal `L` conjugates
of `y_+`, first let the sequence index tend to infinity, then let
that fixed number grow. This makes `E_(A_n)(y_+)` tend to zero.
The reverse leakage again tends to one, the same heights exist,
and all their internal generator commutators tend to zero. Their
native conditional expectations vanish by the internal gap, forcing
the same `1/128` asymptotic external Haar mass. This argument works
in varying finite extensions containing the fixed canonical factor.

The simplicity and `(TT)/T` inputs supply ICC and property `(T)`,
respectively. They are not used to identify an external invariant
space. The argument leaves the construction of an external algebra
with substantial nonnative mass unresolved.
