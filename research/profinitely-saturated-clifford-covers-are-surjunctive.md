---
rg: 2
id: profinitely-saturated-clifford-covers-are-surjunctive
kind: claim
title: Clifford covers over profinitely saturated graphs are surjunctive, even when the center lies in the finite residual
distinct_from:
  separated-finite-normal-subgroups-preserve-surjunctivity: that needs the center to inject into a finite quotient; this reaches covers whose center dies in every finite quotient, by local embeddings into separated covers.
  kun-thom-nonsofic-wreaths-are-surjunctive: that proves the lamp wreath W surjunctive by marked-site peeling; this passes surjunctivity from W to some of its central Z/2 covers.
  clifford-cover-center-separable-iff-graph-is-finite-pullback: that characterizes the separated covers; this proves surjunctivity of a strictly larger class of covers.
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
---

Let `G` be surjunctive, `X` a `G`-set with finitely many orbits, and `S` a `G`-invariant graph. Call `S`
**profinitely saturated** if for every edge `{x,y}`:
1. `x` and `y` are separated by some finite quotient `K\X`;
2. for every non-edge `{x',y'}` of distinct sites, some `K` has `{K x', K y'}` outside the `G`-orbit of
   `{K x, K y}`.

Then the Clifford cover `E_S` is surjunctive.

**ESTABLISHED** by `saturated-clifford-covers-surjunctive-proof` (artifact Section 4, Theorem C).

**Instances.**
- **Finite pullbacks.**
- **Complete graphs** on `X` whenever every point stabilizer is profinitely closed.
- **The cross graph.** For `X = G/Gamma`: `S_cross = { {a Gamma, b Gamma} : a^(-1) b not in Gammabar }`.
  It is a finite pullback exactly when `Gammabar` has finite index.
- **Kun--Thom Theorem E pair.** `Gammabar <= EL_r(F_q[x^(+-1)])` has infinite index, so the center of
  `E_(S_cross)` lies in its finite residual. Yet `E_(S_cross)` is surjunctive, and its quotient is the
  surjunctive wreath `W`.

This settles one instance of the open residue of `finite-normal-subgroups-do-not-affect-surjunctivity`, in
the direction the claim predicts. Soficity of `E_(S_cross)` is not decided here.
