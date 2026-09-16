---
rg: 2
id: thompson-f-guba-sapir-normal-forms-not-automatic
kind: claim
title: No synchronous or asynchronous automatic structure for Thompson's group F over x0, x1 has a language containing the Guba–Sapir normal forms
distinct_from:
  thompson-f-is-automatic: that is the open affirmative answer over any finite generating set; this excludes only languages over {x0, x1} that contain infinitely many of the explicit Guba–Sapir normal-form pairs y x^L and x^L y x^-(L+1) y x^(L+1), so F may still be automatic through another language
  thompson-f-is-not-automatic: that excludes every automatic structure on every generating set; this excludes one family of candidate languages over {x0, x1}
  thompson-f-has-no-near-geodesic-automatic-structure: that excludes languages with bounded additive excess over geodesic length; the Guba–Sapir normal forms have unbounded additive excess, so that theorem does not apply to them, and this exclusion has a different proof
  thompson-f-standard-normal-forms-not-automatic: that concerns the telescoped Cannon–Floyd–Parry normal forms and the pairs x_n^-1, x_1 x_(n+1)^-1; this concerns the Guba–Sapir normal forms and a different family of pairs
artifacts:
  - research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md
---

Proved in `thompson-f-guba-sapir-normal-forms-not-automatic-proof`.

**Setting.** `F` is Thompson's group with the Cannon–Floyd–Parry presentation
`< x0, x1 | [x0 x1^-1, x0^-1 x1 x0], [x0 x1^-1, x0^-2 x1 x0^2] >`. Write
`x = x0`, `y = x1` and `A = {x^±1, y^±1}`. The *Guba–Sapir normal forms* are
the set `N ⊆ A*` of freely reduced words containing no subword `y^ε x^i y` and
no subword `y^ε x^(i+1) y^-1`, where `i >= 1` and `ε = ±1`. This is the
definition displayed in Corwin–Golan–Hermiller–Johnson–Šunić,
*Autostackability of Thompson's group F*, arXiv:1811.11691v1, Section 1. `N` is
a regular language, and CGHJS use it as the normal-form set of their
autostackable structure for `F`.

**Statement.** For `L >= 1` put

    u_L = y x^L,        v_L = x^L y x^-(L+1) y x^(L+1).

Let `L_0 ⊆ A*` be any language that contains `u_L` and `v_L` for infinitely
many `L`. Then `L_0` is not the language of a synchronous automatic structure
for `F` over `A`, and it is not the language of an asynchronous automatic
structure for `F` over `A`, in the sense of Epstein et al., *Word Processing in
Groups* (1992).

Every `u_L` and `v_L` lies in `N`. So the statement applies to `N` itself and to
every language over `A` containing `N`.

**The geometric fact behind it.** `u_L y = v_L` in `F`. Put `a = floor(L/2)`.
The vertex `y x^a` of the Cayley-graph path of `u_L` is at word distance at
least `(a - 1)/2` from every vertex of the path of `v_L`. But the paths of
accepted words `u`, `v` with `ū y = v̄` stay within bounded Hausdorff distance
in both kinds of automatic structure.

**Scope.**

- This does not decide `thompson-f-is-automatic`. It excludes specific
  candidate languages over the fixed alphabet `A`.
- Hauze's theorem (`thompson-f-has-no-near-geodesic-automatic-structure`) does
  not cover `N`: `|v_L| = 3L + 4`, while `v̄_L = ū_L y` has length at most
  `L + 2`.
- Sublanguages of `N`: Guba and Sapir proved that distinct words of `N`
  represent distinct elements. This is Theorem 2 of *The Dehn function and a
  regular set of normal forms for R. Thompson's group F* (J. Austral. Math. Soc.
  Ser. A 62, 1997), known here only as relayed by CGHJS §2.2, since the paper
  was not fetched. Granting it, a sublanguage of `N` that maps onto `F` is `N`
  itself, so it is excluded too. The statement above does not depend on this.
