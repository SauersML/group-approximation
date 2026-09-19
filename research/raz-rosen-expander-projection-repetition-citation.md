---
rg: 2
id: raz-rosen-expander-projection-repetition-citation
kind: route
title: Import Theorems 1 and 2, the expander definition and the closing computation of the proof of Theorem 2 from Raz--Rosen, A Strong Parallel Repetition Theorem for Projection Games on Expanders (ECCC TR10-142; CCC 2012)
target: raz-rosen-expander-repetition-rate-is-quartic-in-gap
requires: []
---

This is a literature import, and credit is the authors' in full. The source is
R. Raz and R. Rosen, *A Strong Parallel Repetition Theorem for Projection Games
on Expanders*, Electronic Colloquium on Computational Complexity, Report No. 142
(2010); CCC 2012, pp. 247--257. The quotations are from the ECCC PDF
(`eccc.weizmann.ac.il/report/2010/142/download/`, 37 pages), with text
extracted by `pypdf` on 2026-09-19. Line breaks are undone. Superscripts and
subscripts, which the extraction flattens, are restored in the obvious way and
marked with `^` and `_`.

* **Abstract.** "We show that if λ is the (normalized) spectral gap of the
  underlying graph, the value of the repeated game is at most
  (1 − ϵ^2)^Ω(c(λ)·n/s), where c(λ) = poly(λ); and if in addition the game is a
  projection game, we obtain a bound of (1 − ϵ)^Ω(c(λ)·n), where
  c(λ) = poly(λ), that is, a strong parallel repetition theorem (when λ is
  constant)."
* **Setting (Section 1.3).** "the underlying distribution P, according to which
  the questions for the two provers are generated, is uniform over the edges of
  a (biregular) bipartite expander graph with sets of vertices X, Y. Let M be
  the (normalized) adjacency matrix of the graph and denote by 1 − λ the second
  largest singular value of M. That is, λ is the (normalized) spectral gap of
  the graph."
* **Section 2.3.2.** "Note that all singular values are between 0 and 1. We
  denote by 1 − λ the singular value whose value is the closest to 1 and that is
  not σ_0. We refer to it as the second singular value. We say that λ is the
  spectral gap of G_XY."
* **Section 2.3.3.** "We define (X, Y, d_X, d_Y, 1−λ)-expander graph to be a
  (d_X, d_Y)-bipartite graph with second singular value 1 − λ."
* **Theorem 1 (Parallel Repetition For General Games).** "For every game G with
  value 1 − ϵ where ϵ < 1/2, the value of G^⊗n is at most
  (1 − ϵ^2 · c(λ))^(n/ log s) where s is the size of the answers set and
  c(λ) = (1/32)10^(−12)λ^2/(log(2/λ))^2."
* **Theorem 2 (Parallel Repetition For Projection Games).** "For every
  projection game G with value 1 − ϵ where ϵ < 1/2, the value of G^⊗n is at most
  (1 − ϵ)^(poly(λ)·n)".
* **Proof of Theorem 2, footnote 5.** "where ϵ′ = 10^(−6)ϵλ/ log(2/λ)".
* **Proof of Theorem 2, first stage, display (32).** "We showed that the value
  of the game G^⊗10^4(ϵ′)^(−1)λ^(−1) is at most
  (1 − 10^(−14) · ϵ · λ/ log(2/λ))^(log(2/λ)ϵ^(−1)) ≤ 1 − 10^(−15) · λ (32)".
* **Proof of Theorem 2, second stage.** "We now state Rao's theorem ([23]
  Theorem 4): There is a universal constant c > 0 such that if G is a projection
  game with value at most 1 − ϵ, the value of G^⊗n is at most (1 − cϵ^2)^n. We
  think of the game G played n times in parallel as the game
  G^⊗10^4(ϵ′)^(−1)λ^(−1) played n · 10^(−4)(ϵ′)λ times in parallel. Thus
  combining Equation (32) with Rao's theorem, we obtain that the value of G^⊗n
  is at most (1 − Ω(λ^2))^(n·10^(−4)(ϵ′)λ) ≤ (1 − ϵ · poly(λ))^n".

These quotations are the whole of the proof's quantitative content, and the
last display is where the polynomial in Theorem 2 is defined. The target claim
records only the arithmetic consequences of these displays.
