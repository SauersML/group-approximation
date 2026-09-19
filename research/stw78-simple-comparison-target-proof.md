---
rg: 2
id: stw78-simple-comparison-target-proof
kind: route
title: Convert quasitraceless comparison into strong pure infiniteness and absorb the map
target: stw78-simple-comparison-targets-force-oinfinity-stability
requires:
  - stw77-quasitraces-detect-stably-finite-corner-quotients
---

The simple almost-unperforated dichotomy says that a sigma-unital simple
C*-algebra with almost-unperforated `W` is either purely infinite or is
stably finite and admits a nonzero `2`-quasitrace.  In the present unital
case a nonzero quasitrace normalizes at the unit.  The second alternative is
excluded, so `B` is simple purely infinite.  A simple purely infinite
C*-algebra is strongly purely infinite.

Now let `phi:A->B` be nuclear.  Gabe's Theorem 9.7 says that every nuclear
homomorphism from a separable exact domain into a strongly purely infinite
codomain is strongly `O_infinity`-stable.  It applies to `phi`, and strong
`O_infinity`-stability implies `O_infinity`-stability.

For the stated unital specialization, nuclearity of the domain makes the
homomorphism nuclear.  The first assertion applies without a fullness
hypothesis.

Finally, Rordam's almost-unperforation theorem gives almost-unperforated
`W(B)` whenever `B` is `Z`-stable.  No permanence or nuclearity assumption
on the target is used.
