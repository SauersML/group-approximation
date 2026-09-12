---
rg: 2
id: scalar-two-root-rank-data-cannot-force-the-identity
kind: claim
title: Conjugation invariance and root subadditivity of the two-root rank function admit nonzero Boolean solutions
distinct_from:
  finite-subgroup-rank-data-cannot-force-two-root-identity: that calibrates per-finite-subgroup rank profiles through the free profile; this calibrates the scalar function delta(a,b) = rk(n_23(b) n_12(a)) under conjugation in all of GL_3(R) and root subadditivity, including every compressor move.
  dyadic-root-displacement-data-admit-trivial-plus-free-models: that calibrates the one-root displacement function; this calibrates the two-root product rank.
artifacts:
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Let `R = L_(F_2)(1,2)`. For a characteristic-two rank model of `EL_3(R)` put
`delta(a,b) = rk(n_23(b) n_12(a))`, so the gate is `delta(1,1) = 0`. Then `delta` satisfies:
* (i) invariance under simultaneous conjugation of root pairs by `GL_3(R)`;
* (ii) subadditivity in each argument;
* (iii) vanishing when either argument is `0`.

For every `eps` in `[0,1]`, the function `eps [a != 0][b != 0]` also satisfies (i)–(iii). So no
argument that uses only these scalar relations proves the gate.

In particular:
* under unit and compressor moves (`compressors-conjugate-leak-free-root-pairs`), `(1,1)` is
  equivalent only to unit pairs;
* the Cuntz decomposition gives only upper bounds on `delta(1,1)`;
* a proof must use operator identities beyond rank data, or a lower bound from orthogonality.

**ESTABLISHED** by `scalar-two-root-rank-data-calibration-proof`.
