---
rg: 2
id: authenticated-opnorm-challenge-compiler
kind: claim
title: A threshold-free operator-norm compiler exists from one marked MF-radical seed
distinct_from:
  marked-mf-radical-seed-gives-proof-triggered-compiler: that is the generic one-generator switch theorem; this instantiates it at the literal non-MF mark and closes the formerly open compiler endpoint.
  threshold-free-reverse-kleene-mf-higman: that is the fixed-point implication after a compiler is supplied; this provides the compiler.
artifacts:
  - research/artifacts/seeded-self-aware-mf-switch-2026-08-23.md
---

**ESTABLISHED AS STATED (2026-08-23), by a simpler seeded switch.**  There is a
total computable map from a Turing-machine index `e` to a finite alphabet, a
uniformly recursively enumerable ordinary group presentation

```text
Gamma_e=<S_e|R_e>,
```

and a marked word `w_e`, such that

```text
e halts     => w_e!=1 in Gamma_e,
e nonhalts  => w_e lies in Res_MF(Gamma_e).
```

Take the literal finitely presented group `E` with its nontrivial invisible
mark `w`.  Adjoin one fresh generator `s`; emit the relators of `E` immediately
and emit `s=1` exactly when `e` halts.  The halting branch is `E`, and the
nonhalting branch is `E*Z`.  Free-factor injectivity keeps `w` nontrivial, and
MF-radical functoriality puts it in `Res_MF(E*Z)`.

This closes the extensional compiler claim without matrix self-detection,
support-profile authentication, a dimension oracle, or quantitative error
moduli.  It also shows that the bare TFM1--TFM2 interface is not an independent
route to the first non-MF group: by `threshold-free-mf-compiler-equivalence`,
it is exactly equivalent to already having one marked MF-radical seed.

The original finite signed-permutation CPU programme remains recorded in
`authenticated-opnorm-compiler-assembly` as a stronger seed-free
implementation problem.  Its two open support/return inputs are not needed
for the unconditional self-aware endpoint.
