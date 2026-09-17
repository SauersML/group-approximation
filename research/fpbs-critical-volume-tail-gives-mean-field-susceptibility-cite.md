---
rg: 2
id: fpbs-critical-volume-tail-gives-mean-field-susceptibility-cite
kind: route
title: Import Hutchcroft's gamma at most delta minus one inequality at delta two
target: fpbs-critical-volume-tail-gives-mean-field-susceptibility
requires: []
---

Citation import, not a reproof. Source: Tom Hutchcroft, *New critical exponent
inequalities for percolation and the random cluster model*, arXiv:1901.10363.
The TeX source `Inequality_New.tex` was fetched 2026-09-17 from
`https://arxiv.org/e-print/1901.10363`. Markup is transcribed.

* Lines 254-273, Theorem `thm:gammadelta_percolation`:
  "Let $G$ be an infinite, connected, locally finite transitive graph, and
  suppose that there exist constants $C>0$ and $\delta >1$ such that
  \[ \bP_{p_c}\left(|K| \geq n\right) \leq C n^{-1/\delta} \]
  for every $n\geq 1$. Then the following hold: [...]
  \item There exists a constant $C''$ such that
  \[ \bE_p\left[|K|^k\right] \leq k!\left[\frac{C''}{p_c-p}\right]^{(\delta-1) + (k-1)\delta } \]
  for every and $0\leq p < p_c$ and $k\geq 1$."
  The words "for every and" are a typo in the source.
* Abstract: the paper proves that "$\gamma \leq \delta-1$ and
  $\Delta \leq \gamma +1$ hold for percolation and the random cluster model on
  any transitive graph".

**Specialization.** Take `delta = 2` and `k = 1`. Then `k! = 1` and the exponent
`(delta-1) + (k-1)delta` equals `1`, so `E_p|K| <= C''/(p_c-p)` for
`0 <= p < p_c`. On a transitive graph `E_p|K| = chi_p` does not depend on the
vertex.
