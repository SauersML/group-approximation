---
rg: 2
id: lang-weil-point-count-citation
kind: route
title: Import the Lang–Weil point count for varieties over finite fields (Lang–Weil 1954, as stated by Tao)
target: lang-weil-point-count
requires: []
---

Citation import, not a reproof. The statements were read on 2026-09-17 from T. Tao, "The Lang–Weil bound", blog post
of 2012-08-31 (terrytao.wordpress.com/2012/08/31/the-lang-weil-bound/). It cites S. Lang and A. Weil, *Number of
points of varieties in finite fields*, Amer. J. Math. 76 (1954), MR 65218.

**Conventions (quoted).** `F` is a finite field with algebraic closure `F̄`. A variety is
"V = { x ∈ F̄^d: P_1(x) = … = P_m(x) = 0 }". It has "complexity at most M" when "d, m, and the degrees of the
P_1,…,P_m are all less than or equal to M". `V(F)` is the set of points of `V` with coordinates in `F`.

**Theorem 2 (quoted).** "Let V be a variety of complexity at most M. Assume that V is defined over F, and that V is
irreducible as a variety over F̄. Then |V(F)| = (1 + O_M(|F|^{-1/2})) |F|^{dim(V)}."

**Corollary 4 (quoted).** For `V` of complexity at most `M` defined over `F`,
"|V(F)| = (c(V) + O_M(|F|^{-1/2})) |F|^{dim(V)}". Here `c(V)` is "the number of top-dimensional components of V
... that are definable over F, or equivalently are invariant with respect to the Frobenius endomorphism". Tao adds:
"the Frobenius endomorphism preserves V itself, but may permute the components of V around. In this case, c(V) is
the number of fixed points of this permutation action of Frobenius on the components."

**Form used downstream.** Let `V` be defined over `F_p` by fixed polynomials, of dimension `e`.
- (LW-up) There is `C_V`, independent of `q`, with `|V(F_q)| <= C_V q^e` for every power `q` of `p`. This uses
  `c(V) <=` the number of irreducible components, which is finite.
- (LW-low) If `V` is nonempty, there are `a >= 1` and `j_0` with `|V(F_q)| >= q^e / 2` for `q = p^{aj}`, `j >= j_0`.
  The `p`-power Frobenius permutes the finitely many top-dimensional components, so some power `p^a` fixes all of
  them. Then `c(V) >= 1` over every `F_{p^{aj}}`, and the error term is below `1/2` for large `j`.
