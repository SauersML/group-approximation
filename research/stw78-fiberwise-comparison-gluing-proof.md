---
rg: 2
id: stw78-fiberwise-comparison-gluing-proof
kind: route
title: Make every unital fiber purely infinite and glue O-infinity absorption over the base
target: stw78-finite-dimensional-simple-fiber-targets-solve-map
requires:
  - stw78-simple-comparison-targets-force-oinfinity-stability
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

For `x in X`, the fiber map

```text
pi_x:B->B_x
```

is a unital quotient map because `B_x` is nonzero.  A normalized
`2`-quasitrace on `B_x` would compose with `pi_x` to give one on `B`.
Therefore every fiber is quasitraceless.

Each `B_x` is separable and nuclear, since both properties pass to
quotients.  The simple almost-unperforated dichotomy used in
`stw78-simple-comparison-targets-force-oinfinity-stability` now makes `B_x`
simple purely infinite, hence strongly purely infinite.  Nuclear
Kirchberg absorption then gives

```text
B_x ~= B_x tensor_min O_infinity                         (1)
```

for every `x`.

The global step is an imported fiber theorem, not an extension argument.
Hirshberg--Rordam--Winter, Theorem 4.6 in
[*C_0(X)-algebras, stability and strongly self-absorbing
C*-algebras*](https://arxiv.org/abs/math/0610344), says that if `D` is
`K_1`-injective and strongly self-absorbing, `X` is locally compact,
metrizable, and finite-dimensional, and `C` is a separable `C_0(X)`-algebra,
then `C` is `D`-stable exactly when every fiber `C_x` is `D`-stable.
The Cuntz algebra `O_infinity` has the required properties.  Apply that
theorem to (1) to obtain

```text
B ~= B tensor_min O_infinity.                            (2)
```

Kirchberg--Rordam's absorption theorem makes (2) strongly purely infinite.
Finally, Gabe's Theorem 9.7 says that every nuclear homomorphism from a
separable exact domain into a strongly purely infinite codomain is strongly
`O_infinity`-stable.  This proves the map statement.  An LXXVIII map is
nuclear because its domain is nuclear.

This proof evades the nonunital-layer obstruction rather than assuming it
away.  Ambient quasitracelessness need not exclude an unbounded trace on a
nonunital ideal, but it does pass to each nonzero unital fiber quotient.
Finite covering dimension is essential to the imported gluing theorem;
Hirshberg--Rordam--Winter give infinite-dimensional-base counterexamples to
fiberwise absorption.  No conclusion is claimed there.
