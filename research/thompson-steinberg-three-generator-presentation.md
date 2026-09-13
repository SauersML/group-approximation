---
rg: 2
id: thompson-steinberg-three-generator-presentation
kind: claim
title: The binary Leavitt unit group has a presentation with three generators and sixteen relators
distinct_from:
  thompson-steinberg-presentation-of-leavitt-unit-group: that is the four-generator, eighteen-relator form over Bleak--Quick's three-generator V, total length 322; this uses their two-generator V, so it has one generator and two relators fewer, but total length 467.
  leavitt-unit-group-steinberg-weyl-presentation: that is the seven-generator, sixty-relator presentation over S_5; this is over Thompson's V.
---

**ESTABLISHED (2026-09-12, unreviewed)** through `thompson-steinberg-three-generator-presentation-proof`.

```text
L_(F_2)(1,2)^x = < u, v, x |  seven relators of Bleak--Quick Theorem 1.3,
                    x^2,  (u^3 x)^3,  [x, iota_1(u)],  [x, iota_1(v)],
                    [x, {}^(v^-1u^3vu^2v^-1) x],  [x, {}^(v^-1) x],  [x, {}^(u^3v^-1u) x],
                    [x, {}^(u^3v^-1) x] = {}^(v^-1) x,
                    {}^(uv^-1u^-1v^-1u^-1v^-1) x . {}^(uv^-1uv^-1uv^-1) x = x >
```

The images are `u -> t_(00,01) t_(10,110) t_(10,111)`, `v -> (01 10 11)` (maps on the right,
realized as `U_g^-1`), and `x -> 1 + S[00]T[01]`. Here `iota_1(u)` and `iota_1(v)` are the
products of three and two conjugates of `u^3` listed in the artifact. Total literal length is
467 and the longest relator has length 108.

So `L_(F_2)(1,2)^x` is a finitely presented simple nonsofic Kazhdan group with three generators
and sixteen relators. Since the group is perfect with `H_2 = 0`, the only lower bound known here
is deficiency at most `0`, which allows as few relators as generators. Whether a balanced
presentation exists is not known here.
