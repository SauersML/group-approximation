---
rg: 2
id: thompson-f-word-length-is-comparable-to-caret-count-citation
kind: route
title: Import the Burillo--Cleary--Stein comparison of word length and caret count in F(p), p = 2
target: thompson-f-word-length-is-comparable-to-caret-count
requires: []
---

Citation import. No proof is re-derived here.

J. Burillo, S. Cleary, M. Stein, *Metrics and embeddings of generalizations of
Thompson's group F*, arXiv:math/9809185 (v1 30 Sep 1998, revised 14 Dec 1998).
The arXiv listing gives the journal reference Trans. Amer. Math. Soc. 353 (2001),
no. 4, 1677–1689. Read on 2026-09-16 from the arXiv abstract page and from the
arXiv PDF, whose text was extracted mechanically.

- **Abstract, verbatim (arXiv abstract page):** "The distance from the origin in
  the word metric for generalizations F(p) of Thompson's group F is
  quasi-isometric to the number of carets in the reduced rooted tree diagrams
  representing the elements of F(p)."
- `F = F(2)`. The generating set is `x_0, …, x_{p-1}`, which is `{x_0, x_1}` for
  `p = 2`. For finitely generated groups, "quasi-isometric to" means exactly the
  two-sided linear comparison in the target claim.
- **Body, as extracted from the PDF.** Fraction bars and inequality signs were
  lost in extraction, so the reading below is a reconstruction.
  - Theorem 1 defines `D(x) = r_1 + … + r_n + s_1 + … + s_m + i_n + j_m` from the
    normal form `x = x_{i_1}^{r_1} ⋯ x_{i_n}^{r_n} x_{j_m}^{-s_m} ⋯ x_{j_1}^{-s_1}`
    and states `D(x)/(3(p-1)) ≤ |x|_p ≤ 3D(x)`.
  - Theorem 3 gives the caret count of the reduced diagram as
    `N(x) = max{ i_k + r_k + … + r_n + 1 ; j_l + s_l + … + s_m + 1 }`. It "is
    equivalent to the distance", with the inequalities `D(x)/4 ≤ N(x) ≤ D(x)+1`
    in its proof.
  - Sanity check of the reconstruction. For `x_0`: `D = 1`, `N = 2`, `|x_0| = 1`.
    For `x_1`: `D = 2`, `N = 3`, `|x_1| = 1`. Both fit the inequalities.
  - Reading them this way gives `|x| ≤ 3D(x) ≤ 12·N(x)` and
    `N(x) ≤ D(x) + 1 ≤ 3|x| + 1`.
- The target claim is only the qualitative statement in the verbatim abstract.
  The explicit constants are recorded here as extracted and are not load-bearing.

Secondary corroboration, abstract only: Burillo–Cleary–Stein–Taback,
arXiv:math/0503670 (Trans. Amer. Math. Soc. 361 (2009) 631–652), verbatim: "We
show that the number of carets in a reduced representative of an element of T
estimates the word length, and that F is undistorted in T."
