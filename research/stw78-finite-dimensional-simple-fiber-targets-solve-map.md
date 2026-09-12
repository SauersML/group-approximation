---
rg: 2
id: stw78-finite-dimensional-simple-fiber-targets-solve-map
kind: claim
title: Finite-dimensional fields with regular simple fibers solve LXXVIII
distinct_from:
  stw78-simple-comparison-targets-force-oinfinity-stability: that assumes the whole target is simple and comparison-regular; this permits a nonsimple target and assumes comparison only in its fibers.
  stw78-countable-ordinal-regular-targets: that glues algebraically simple layers through a countable composition series; this glues unital quotient fibers over a finite-dimensional base and needs no composition series.
artifacts:
  - research/artifacts/stw78-finite-quasitrace-seed-audit-2026-08-30.md
---

Let `X` be a finite-dimensional compact metrizable space and let `B` be a
nonzero unital separable nuclear `C(X)`-algebra.  Suppose every fiber `B_x`
is nonzero, simple, and has almost-unperforated `W(B_x)`.  If `B` has no
normalized `2`-quasitrace, then

```text
B ~= B tensor_min O_infinity.
```

In particular, `B` is strongly purely infinite.  Consequently, for every
separable exact C*-algebra `A`, every nuclear homomorphism

```text
phi:A->B
```

is strongly `O_infinity`-stable.  Every LXXVIII map into such a target is
therefore `O_infinity`-stable.

No simplicity, finite ideal lattice, composition series, global
almost-unperforation, or `Z`-stability of `B` is assumed.  The theorem applies
to nonsimple fields with infinitely many ideals; regularity is required only
in the simple unital fibers.
