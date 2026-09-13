---
rg: 2
id: kazhdan-commutant-compression-stability-is-finitary
kind: claim
title: In every metric approximation class, normalization of Kazhdan centralizers at a rigid pair is a dimension-uniform inequality for approximate representations
distinct_from:
  rigid-compression-defect-normalization-dichotomy: that equates killing rigid defects with normalization inside metric ultraproducts; this turns normalization at one rigid pair into a uniform inequality about approximate representations in each finite dimension, with no ultrafilter, and records which rows hold, fail or stay open.
  kazhdan-asymptotic-commutant-transport: that is the operator-norm transport theorem for asymptotic representations; this is the class-independent finitary equivalence, of which the transport theorem supplies the operator-norm-to-2-norm row.
artifacts:
  - research/artifacts/unified-compression-rigidity-2026-09-12.md
---

**ESTABLISHED.** Let `C` be sofic (`Sym(n)`, normalized Hamming), hyperlinear (`U(n)`,
normalized Hilbert--Schmidt), `k`-linear sofic (`GL_n(k)`, normalized rank) or weak MF
(`U(n)`, operator norm), with model groups `G_n` and bi-invariant metrics `d_n`. Put
`c(x, y) = d_n(xy, yx)`.

Let `Gamma <= G` be Kazhdan groups, `F` a finite symmetric generating set of `Gamma`, and
`T` a finite set of compressors (`t Gamma t^-1 <= Gamma`) with `G = <F cup T>`. An
`(eps, R)`-model is a map `u` from the `R`-ball of `G` to `G_n` with `u_1 = 1` and
`d_n(u_g u_h, u_(gh)) <= eps` whenever `g, h, gh` lie in the ball. Then the following are
equivalent.

```text
(UCS_C)  For every eta > 0 there are eps > 0 and R such that for all n, all
         (eps,R)-models u in G_n and all z in G_n with c(z, u_s) <= eps (s in F):
             c(u_t z u_t^-1, u_s) <= eta        for all s in F, t in T.

(NORM_C) For every metric ultraproduct U of the G_n and every homomorphism
         sigma : G -> U, the group sigma(G) normalizes C_U(sigma(Gamma)).
```

Neither side involves a trace condition, and neither depends on the choice of `(F, T)`.
With `rigid-compression-defect-normalization-dichotomy`, the rigid defect criterion
`DD(C)` holds iff `(UCS_C)` holds for every infranormal Kazhdan pair.

## The rows, read at the Kun--Thom Theorem E pair

- **Sofic: holds.** `sofic-groups-kill-rigid-compression-defects` gives `NORM` for every
  pair.
- **Weak MF: fails.** The amalgam `H_K` of `weak-mf-groups-can-carry-rigid-defects` is MF
  and carries a nontrivial defect over this pair.
- **Operator-norm models, 2-norm capture: holds with only `Gamma` Kazhdan.** Take
  operator-norm models, contractions `z`, and commutators in the normalized 2-norm. The
  same equivalence holds, and `kazhdan-asymptotic-commutant-transport` is the ultraproduct
  side.
- **Hyperlinear and `k`-linear sofic: open.** These are the win--win rows of the ladder
  artifact. The Hilbert--Schmidt instance at explicit compressors is
  [[hs-uniform-compression-stability-at-the-theorem-e-pair]].

## Model test

If every `t in T` normalizes `Gamma`, `(UCS_C)` holds with `eta = O(eps)`. At the Theorem E
pair it holds in the sofic class and fails in the weak MF class. So the proposition is
neither vacuous nor automatic.

Derivation: `kazhdan-commutant-compression-stability-is-finitary-proof`. Artifact, Sections
1, 2 and 5.
