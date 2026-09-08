---
rg: 2
id: affine-normal-form-reduces-three-factor-surjunctivity
kind: route
title: Move each row's nonlinearity to an opposite block with reversible track changes
target: three-factor-finite-alphabet-ca-are-surjunctive
requires:
  - recipient-affine-three-factor-ca-are-surjunctive
artifacts:
  - research/artifacts/gottschalk-recipient-affine-normal-form-and-fiber-obstruction-2026-09-08.md
---

For a CA F on a finite block of R-tracks, add an identity copy of
that block and use the reversible local normal form

    H(x,u)=(x+u,F(x)-x-u).

Each first-block output has coefficient +1 on its own x track and
depends otherwise only on u. Each second-block output has coefficient
-1 on its own u track and depends otherwise only on x. The bound of
three unary factors per term is preserved.

The fiber H^-1(z,w) is canonically F^-1(z+w), via u=z-x. Thus both
injectivity and surjectivity are preserved exactly. The prerequisite
would therefore make every injective F in the target class surjective.
The prerequisite itself is not proved by these reversible changes.
