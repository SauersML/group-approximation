---
rg: 2
id: kerr-nowak-measure-free-group-actions-are-rf-citation
kind: route
title: Kerr–Nowak Theorem 5.2, as quoted verbatim in Ma arXiv:2209.00580
target: kerr-nowak-measure-free-group-actions-are-rf
requires: []
---

**Source read.** Xin Ma, arXiv:2209.00580 (TeX source `main.tex`, fetched on MSI 2026-09-13), remark
after Theorem `thm: topo group of residually finite action`:

> "it was shown in [K-N, Theorem 5.2] that any minimal action of the free group $\F_r$
> ($r\in \N\cup{\infty}$) on the Cantor set is residually finite if it admits an $\F_r$-invariant
> Borel probability measure"

[K-N] = D. Kerr and P. W. Nowak, *Residually finite actions and crossed products*, Ergod. Th. Dynam.
Sys. 32 (2012), 1582–1614 (Ma's bibliography).

**Bound (lifted at review).** The primary paper was NOT read by the lane. arXiv API and Semantic Scholar queries returned HTTP 429.
A reviewer should confirm Theorem 5.2 and its hypotheses from Kerr–Nowak before this import is
relied on outside Theorem C of `un-measure`.

**Primary source (review 2026-09-13, un-verify-measure).** D. Kerr and P. W. Nowak, *Residually finite actions and
crossed products*, Ergod. Th. Dynam. Sys. 32 (2012), 1582–1614, fetched on MSI from Cambridge Core (DOI
10.1017/S0143385711000575). p. 1604:

> "THEOREM 5.2. Let X be a compact metrizable space and F_r ↷ X a minimal continuous action. Then the following are
> equivalent. (1) The action is residually finite. (2) There is an F_r-invariant Borel probability measure on X. (3)
> C(X) ⋊_λ F_r is an MF algebra. (4) C(X) ⋊_λ F_r is stably finite. (5) The action is F_r-finite in the
> Cuntz–Pedersen sense."

§5 opens with "free group F_r, where r ∈ N ∪ {∞}". Definition 2.1 allows a finite G-set E with a map ζ: E → X. The paper
notes that ζ can be taken to be an inclusion E ⊆ X when X has no isolated points, which is Ma's restatement on the Cantor
set. Review: `research/artifacts/un-review-measure-2026-09-13-part1.md` §M4.
