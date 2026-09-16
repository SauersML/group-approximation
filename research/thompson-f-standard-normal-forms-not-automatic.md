---
rg: 2
id: thompson-f-standard-normal-forms-not-automatic
kind: claim
title: No synchronous or asynchronous automatic structure for Thompson's group F over x0, x1 has a language containing the telescoped standard normal forms
distinct_from:
  thompson-f-is-automatic: that is the open affirmative answer over any finite generating set; this excludes only languages over {x0, x1} that contain infinitely many of the explicit pairs x0^-(n-1) x1^-1 x0^(n-1) and x1 x0^-n x1^-1 x0^n, so F may still be automatic through another language
  thompson-f-is-not-automatic: that excludes every automatic structure on every generating set; this excludes one family of candidate languages over {x0, x1}
  thompson-f-guba-sapir-normal-forms-not-automatic: that concerns the Guba–Sapir normal forms and the pairs y x^L, x^L y x^-(L+1) y x^(L+1); this concerns the telescoped Cannon–Floyd–Parry normal forms and a different family of pairs
  thompson-f-has-no-near-geodesic-automatic-structure: that excludes languages with bounded additive excess over geodesic length; this excludes languages containing a specific family of diverging pairs, whatever their excess
artifacts:
  - research/artifacts/guba-sapir-normal-forms-not-automatic-2026-09-16.md
---

Proved in `thompson-f-standard-normal-forms-not-automatic-proof`.

**Setting.** Write `x = x0`, `y = x1` and `A = {x^±1, y^±1}`. Put `x_0 = x`
and `x_n = x^-(n-1) y x^(n-1)` for `n >= 1`. A *standard normal form*
(Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, 1996,
§2) is a word
`x_0^(b_0) ... x_r^(b_r) x_r^-(c_r) ... x_0^-(c_0)` with `b_i, c_i >= 0` such
that if `b_i, c_i > 0` then `b_(i+1) > 0` or `c_(i+1) > 0`. Its *telescoped*
form is the word over `A` obtained by substituting for each `x_n` and freely
reducing. Let `T ⊆ A*` be the set of telescoped standard normal forms.

**Statement.** For `n >= 2` put

    s_n = x^-(n-1) y^-1 x^(n-1),        t_n = y x^-n y^-1 x^n,

the telescoped forms of `x_n^-1` and `x_1 x_(n+1)^-1`. Let `L_0 ⊆ A*` be any
language that contains `s_n` and `t_n` for infinitely many `n`. Then `L_0` is
not the language of a synchronous automatic structure for `F` over `A`, and it
is not the language of an asynchronous automatic structure for `F` over `A`, in
the sense of Epstein et al., *Word Processing in Groups* (1992). In particular
this holds for `T` and for every language over `A` containing `T`.

**The geometric fact behind it.** `s_n y = t_n` in `F`. The vertex `x^-(n-1)`
of the path of `s_n` is at word distance at least `(n - 2)/2` from every vertex
of the path of `t_n`.

**Scope and a correction.**

- Regularity of `T` was not examined. The statement is about every language
  containing infinitely many of the pairs, so it does not reduce to a
  regularity question.
- The earlier Attempts entry on `thompson-f-is-automatic` blames right
  multiplication by `x0`. That multiplier is harmless for `T`: the telescoped
  normal form of `g x0` is the free reduction of that of `g` followed by `x`
  (artifact §7). The divergence comes from the multiplier `x1`.
- This does not decide `thompson-f-is-automatic`.
