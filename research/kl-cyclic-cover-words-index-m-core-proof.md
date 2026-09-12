---
rg: 2
id: kl-cyclic-cover-words-index-m-core-proof
kind: route
title: Eliminate the variable power with the equation and read off the shift
target: kl-cyclic-cover-words-have-an-index-m-core
requires: []
---

**1.**  In `H`, `t^m = C^(-1)`, so `t` commutes with `C`.  Also
`t G_i t^(-1) = G_(i+1)` for `i < m-1` and
`t G_(m-1) t^(-1) = t^m G_0 t^(-m) = C^(-1) G_0 C`, so `t D t^(-1) <= D`.
Conversely `t^(-1) G_i t = G_(i-1)` for `i >= 1`, and
`t^(-1) G_0 t = t^(m-1) (C G_0 C^(-1)) t^(-(m-1)) = C G_(m-1) C^(-1)`,
because `t^(m-1)` commutes with `C`.  Hence `D` is normal, `H = D <t>`,
and `t^m in D`.  The degree map `H -> C_m` kills `D` and sends `t` to a
generator, so its kernel `D <t^m>` equals `D`.  The injectivity statement
follows because `G_0` is the image of `G`.

**2.**  `N_m = ker(F -> C_m) = P * <z>` with `z = t^m`, and `F` is the union
of the cosets `t^i N_m`, `0 <= i < m`.  So `<<w>>_F` is the normal closure in
`N_m` of the elements `t^i w t^(-i) = alpha^i(C) z`, where `alpha = Ad(t)`
sends `g_j` to `g_(j+1)` for `j < m-1` and `g_(m-1)` to `z g_0 z^(-1)`.
For `i <= m-1` and `j <= m-1`, `alpha^i(g_j)` is `g_(j+i)` or
`z g_(j+i-m) z^(-1)`.  Tietze-eliminate `z = C^(-1)` with the `i = 0`
relator.  The remaining relators become `rho_i(C) C^(-1)`.

**3.**  `C in G`, and `t |-> C^(-1)` defines a retraction `H -> G`.

**4.**  Substitute `m = 2`, so that `rho_1(g_0) = g_1` and
`rho_1(g_1) = C^(-1) g_0 C`.  The trailing `C C^(-1)` cancels.  Counting
syllables: `K` copies of `C^(-1)` and `K - 1` copies of `C`, each of length
`2K`, together with the `2K` letters `a_i'`, `b_i`, give `4K^2` letters.
The junctions `a_1' | C^(-1)` and `C^(-1) | b_K` each merge two syllables
into one.  The `K - 1` junctions `C^(-1) | b_i | C` and the `K - 1`
junctions `C | a_(i+1)' | C^(-1)` each merge three into one.  That removes
`4K - 2` syllables.  The merged syllables are `(a_1 b_K^(-1))'`,
`a_1^(-1) b_i a_1`, `(b_K a_(i+1) b_K^(-1))'` and `a_1^(-1) b_K`.  They are
nontrivial under the stated hypotheses.  The word starts in `G_1` and ends
in `G_0`, so it is cyclically reduced.

Exponent pattern: the syllable heights alternate `0, 1`, so the exponents
between consecutive syllables are `+1, -1, ..., +1`, and the closing `t^2`
contributes the final `+1`.  Cyclically this gives `(+-)^(K-1) ++`.
