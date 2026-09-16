---
rg: 2
id: finite-evc-iff-finite-efin-commensurator-models-proof
kind: route
title: Forward by commensurator restriction, reverse by the Lück–Weiermann pushout of finite complexes
target: finite-evc-iff-finite-efin-and-commensurator-models
requires:
  - finite-evc-model-restricts-to-commensurators
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

Full proof: Theorem 2 of `research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md`.
Sources: Lück–Weiermann, arXiv:math/0702646, read from the PDF on 2026-09-16.

**Forward.** Let `X` be a finite model for `E_VC G`.

- (a) is Lück–Weiermann Corollary 5.4(ii).
- (b): every infinite virtually cyclic `H` fixes a point, so `H <= gG_σg^{-1}` for a
  representative cell `σ`. Then `[H] = g[G_σ]g^{-1}`, which gives at most as many orbits of
  classes as there are orbits of cells.
- (c) is `finite-evc-model-restricts-to-commensurators`. Conjugating a model for `N_G[C]` gives a
  model for `N_G[gCg^{-1}] = gN_G[C]g^{-1}`, so one representative per orbit suffices.

**Reverse.** Use Lück–Weiermann Theorem 2.3 with `F = FIN`, `G = VC` and commensurability, for
which properties (2.1) hold. Let `I` be the finite set of representatives from (b), and for each
`C` in `I` put `N = N_G[C]`.

- By (c), `N` has a finite model `Y` for `E_{G[C]}(N)`.
- Members of `G[C]` are virtually cyclic and have finite `E_FIN` models, so Proposition 5.1(ii)
  gives a finite model `Z` for `E_FIN N`.
- By Remark 2.5, choose cellular maps `i : ∐_{C in I} G ×_N Z -> E_FIN G` and `f : Z -> Y`.
  Replace the finite `E_FIN G` from (a) by the mapping cylinder of `i`. That is again a finite
  model, and it makes `i` an inclusion.
- The `G`-pushout of Theorem 2.3 is then a model for `E_VC G`. Its cells are those of
  `∐ G ×_N Y` together with the cells of `cyl(i)` outside the image of `i`. There are finitely
  many orbits, because `I` is finite and each complex involved is finite.
