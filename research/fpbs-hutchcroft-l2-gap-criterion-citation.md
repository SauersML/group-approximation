---
rg: 2
id: fpbs-hutchcroft-l2-gap-criterion-citation
kind: route
title: Import sharpness, the l2 Aizenman-Barsky bound, the Cheeger lemma and the criterion from Percolation on hyperbolic graphs
target: fpbs-hutchcroft-l2-gap-criterion
requires: []
---

Citation import, not a reproof. Source: Tom Hutchcroft, *Percolation on
hyperbolic graphs*, arXiv:1804.10191. The TeX source
`HyperbolicPercolation6.tex` was fetched 2026-09-17 from
`https://arxiv.org/e-print/1804.10191`. Line numbers refer to that file and
agree with `research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md`.
Markup is transcribed.

* **Item 1, lines 285-286 and 299.** "It follows by sharpness of the phase
  transition [...] that if $G$ is quasi-transitive then
  $\|T_p\|_{1\to1}<\infty$ if and only if $p<p_c$." Line 299: "In particular,
  \[p_c(G)=p_{1\to 1}(G)=p_{\infty\to\infty}(G)\leq p_{q\to q}(G)\leq p_{2\to 2}(G)\]
  for every quasi-transitive graph $G$ and $q\in [1,\infty]$." Line 288
  defines `p_(q->q)` as in the claim. Line 486 writes
  "$\|T_p\|_{1\to 1}=\overline{\chi}_p$".
* **Item 2, lines 448-453,** `cor:l2AizBar`: "Let $G$ be an infinite,
  connected, locally finite graph. Then
  \[\|T_p\|_{q\to q} \geq \frac{1-p}{\|A\|_{q\to q}(p_{q\to q}-p)} \]
  for every $0\leq p<p_{q\to q}$. In particular,
  $\|T_{p_{q\to q}}\|_{q\to q}=\infty$."
* **Definition of iota, lines 504-508:** "For each $0\leq p<p_c$, we define
  \[ \iota(T_p) = 1 - \sup\left\{ \frac{\sum_{u,v\in K} \tau_{p}(u,v)}{\overline{\chi}_{p} |K|} : K \subseteq V \text{ finite} \right\}. \]"
* **Item 4, lines 513-521,** `prop:criterion`: "Let $G$ be a connected, locally
  finite, quasi-transitive graph. Then $p_c(G)<p_{2\to2}(G)$ if and only if
  \[ \liminf_{p\uparrow p_c} \frac{p_c-p}{1-p} \overline{\chi}_{p} \sqrt{1-\iota(T_p)^2} < \frac{1}{\|A\|_{2\to2}}. \]
  In particular, if [this] holds then $p_c(G)<p_u(G)$ and
  $\nabla_{p_c}<\infty$."
* **Item 3, lines 528-534,** `lem:Cheeger`: "Let $G$ be a connected, locally
  finite graph. Then
  \[ \overline{\chi}_p \left(1-\iota(T_p)\right) \leq \|T_p\|_{2\to2} \leq \overline{\chi}_p \sqrt{1-\iota(T_p)^2} \]
  for every $0<p<p_{1\to 1}(G)$." Lines 538-539 prove it by Cheeger's
  inequality for the symmetric substochastic matrix
  `chi-bar_p^(-1) T_p`.
