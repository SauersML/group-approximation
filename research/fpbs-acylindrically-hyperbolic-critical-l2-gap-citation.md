---
rg: 2
id: fpbs-acylindrically-hyperbolic-critical-l2-gap-citation
kind: route
title: Import the two Choi-Seo estimates and apply Hutchcroft's l2 criterion
target: fpbs-acylindrically-hyperbolic-critical-l2-gap
requires: []
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
---

This route is a citation import followed by a short, complete deduction. Both
sources were read from their arXiv e-print TeX sources on 2026-09-16. Line
numbers refer to those files. Sections 2 and 3 of the artifact have the quotes
and the proof.

**Imports.**

* [H] Hutchcroft, *Percolation on hyperbolic graphs*, arXiv:1804.10191, file
  `HyperbolicPercolation6.tex`.
  - `prop:criterion`, label line 514, statement lines 515–520: "Let G be a
    connected, locally finite, quasi-transitive graph. Then
    p_c(G)<p_{2→2}(G) if and only if liminf_{p↑p_c} ((p_c−p)/(1−p))
    χ̄_p sqrt(1−ι(T_p)^2) < 1/‖A‖_{2→2}."
  - Here `iota(T_p) = 1 - sup_K sum_(u,v in K) tau_p(u,v)/(chi-bar_p |K|)`,
    lines 504–508.
  - The "if" direction, lines 542–543, uses `lem:Cheeger` (label line 529)
    and `cor:l2AizBar` (label line 449).
* [CS] Choi–Seo, *Percolation in acylindrically hyperbolic groups*,
  arXiv:2508.08932v2, file `perc.tex`.
  - Their Cayley graph on a finite generating set `S` uses the edges indexed
    by `S union S^(-1)`, as a simplicial graph (lines 204 and 357).
  - `thm:main`, label line 216: `p_c(Gamma)<p_u(Gamma)` for every Cayley graph
    of an acylindrically hyperbolic group.
  - (Gamma1), line 540: `limsup_(p->p_c-) (p_c-p) chi_p < infinity`.
  - (Gamma2), lines 541–542: `lim_(p->p_c-) sup_(A finite) sum_(g,h in A)
    tau_p(g,h)/(chi_p #A) = 0`.
  - `thm:hutchcroft1plus2`, label line 561, gives (Gamma1) from a geometric
    hypothesis. Line 1537 reads "Therefore acylindrically hyperbolic groups
    satisfy the assumption of Theorem `thm:hutchcroft1plus2`."
  - `cor:hutchcroftIotaAcyl`, label line 2195: "Let Γ be the Cayley graph of an
    acylindrically hyperbolic group G. Then Equation (Gamma2) holds."

Choi–Seo's refereeing status was not verified. The metadata fetched on
2026-09-16 show v2 of 2025-08-13 and no journal reference.

**Deduction.**

* `Gamma` is connected and transitive, and `||A||_(2->2) <= deg < infinity`.
  On a Cayley graph `chi_p(v)` does not depend on `v`, so `chi-bar_p=chi_p`.
  Also `p_c>0`.
* By `thm:main`, `p_c<p_u<=1`.
* By (Gamma1) there are `M` and `p_1 in (0,p_c)` with `(p_c-p)chi_p <= M+1`
  on `(p_1,p_c)`.
* Put `s(p) = 1-iota(T_p)`. Taking `K={e}` gives `s(p) >= 1/chi_p > 0`. Since
  `sum_(h in K) tau_p(g,h) <= chi_p`, also `s(p) <= 1`.
* So `1-iota(T_p)^2 = s(p)(2-s(p)) <= 2s(p)`, and `s(p)->0` by (Gamma2).
* For `p in (p_1,p_c)`:

      (p_c-p)/(1-p) chi-bar_p sqrt(1-iota(T_p)^2) <= (M+1)/(1-p_c) sqrt(2 s(p)) -> 0.

* The liminf in `prop:criterion` is `0 < 1/||A||_(2->2)`. So
  `p_c(Gamma)<p_(2->2)(Gamma)`.
