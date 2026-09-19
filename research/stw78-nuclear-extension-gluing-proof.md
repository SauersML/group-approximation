---
rg: 2
id: stw78-nuclear-extension-gluing-proof
kind: route
title: Stabilize, absorb O-infinity, and use D-stability permanence
target: stw78-nuclear-strong-pi-extension-gluing
requires: []
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

For a separable nuclear strongly purely infinite algebra `C`, its
stabilization `C tensor K` remains strongly purely infinite.  Kirchberg--
Rordam, *Infinite non-simple C-star algebras: absorbing the Cuntz algebra
O-infinity*, Advances in Mathematics 167 (2002), Theorem 8.6, makes the
stable algebra `C tensor K` `O_infinity`-stable.  Toms--Winter, *Strongly
self-absorbing C-star algebras*, Corollaries 3.1 and 3.2, pass this absorption
from the stabilization back to `C`.  Thus separable nuclear strong pure
infiniteness implies `O_infinity`-stability.  The reverse implication is
Kirchberg--Rordam, Proposition 5.12.

Now apply Toms--Winter Theorem 4.3 with `D=O_infinity`.  Its hypotheses are
exactly a short exact sequence of separable C-star algebras and a separable,
unital, strongly self-absorbing, `K_1`-injective `D`.  It turns absorption in
`J` and `Q` into absorption in `E`; Proposition 5.12 then makes `E` strongly
purely infinite.

For the filtration statement, finite induction makes every `E_n`
`O_infinity`-stable.  Toms--Winter Corollary 3.4 says that a sequential
inductive limit of separable `D`-stable algebras is `D`-stable.  Since the
inclusions have limit `E`, it follows that `E` is `O_infinity`-stable and
hence strongly purely infinite.
