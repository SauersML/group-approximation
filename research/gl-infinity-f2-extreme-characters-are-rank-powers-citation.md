---
rg: 2
id: gl-infinity-f2-extreme-characters-are-rank-powers-citation
kind: route
title: Import the Thoma--Skudlarek list of extreme characters of GL(infinity,q) verbatim from two secondary sources
target: gl-infinity-f2-extreme-characters-are-rank-powers
requires: []
---

**Primary source (not read here).** H.-L. Skudlarek, *Die unzerlegbaren Charaktere einiger diskreter
Gruppen*, Math. Ann. 223 (1976), 213--231. The conjecture is E. Thoma, *Characters of the group
GL(infinity,q)*, Lecture Notes in Math. 266 (1972), 321--323.

**Secondary source 1.** A. Gnedin, V. Gorin, S. Kerov, *Block characters of the symmetric groups*,
arXiv:1108.5044v3 (J. Algebraic Combin. 38 (2013)). The PDF was fetched from arxiv.org and read on
2026-09-18. Section 8, "Connection to the characters of the linear groups over the Galois fields",
quoted verbatim (ligatures and line breaks normalized, `ǫ` written `ε`):

> The group GL∞(q) is the group of infinite matrices of the kind g = ( h 0 ; 0 1∞ ) where h is a finite
> square matrix with coefficients from the Galois field Fq with q elements, 1∞ denotes the infinite unit
> matrix, and 0's are zero matrices of suitable dimensions. From this definition it is clear that the
> group has the structure of inductive limit GL∞(q) = ∪n≥1 GLn(q). Thoma [35] conjectured that all
> extreme normalized characters of GL∞(q) are of the form
>
> χ(g) = ε(det g) q^(−m c(g)), m ∈ Z≥0 ∪ {∞}, (26)
>
> where ε is a one-dimensional character of the cyclic group F∗q, and c(g) is the rank of the matrix
> g − Id. The conjecture was proved by Skudlarek [29].

Their [29] is Skudlarek, Math. Ann. 223 (1976). ("2130–231" is a typo in their bibliography.)

**Secondary source 2.** A. Gnedin, S. Kerov, *Derangement characters of the finite general linear group*,
arXiv:math/0406614v1. The PDF was fetched from arxiv.org and read on 2026-09-18. Section 1, quoted
verbatim (the exponent in (1) is lost in text extraction; the normalized form is restated in Section 6,
quoted below):

> Denote 1n the unit matrix and for g ∈ Gn let r(g) = dim ker(g − 1n) be the number of Jordan blocks to
> the eigenvalue 1. [...] Our interest in the derangement characters is motivated by the Thoma–Skudlarek
> classification of characters of the infinite group GL(∞,q) = ∪Gn. As was conjectured by Thoma [5] and
> then proved by Skudlarek [3], any positive definite class function f : GL(∞,q) → C satisfying
> f(1∞) = 1 can be uniquely represented as a convex combination of the functions σk · χ where σk is the
> normalized version of (1) and χ is a linear character. For the special linear group SL(∞,q) the
> one-dimensional factor is trivial and all positive definite class functions are of derangement type.
> [...] the Thoma-Skudlarek result identifies all possible pointwise limits of (rather complicated)
> characters of finite groups Gn

Section 6, verbatim:

> Given z ∈ C consider the derangement function fz(g) = z^(n−r(g)). This definition is consistent for
> different n because r(g ⊕ 1) = r(g) + 1, thus fz is defined on the infinite group G∞ = ∪Gn. Obviously,
> for z = 0, fz is the normalized regular character equal to δ1∞,g, while for z = q^(−k) it is the
> normalized Thoma character σk := σ(n)k / dim σ(n)k = q^(−k(n−r(g))). Skudlarek proved that for z ≠ 0
> the only positive definite functions among fz are Thoma characters (see [3], Behauptung 3).

Their [3] is Skudlarek, Math. Ann. 223 (1976), 213--231.

**Reading.**
* `n − r(g) = rank(g − 1)`, so `σ_k(g) = q^(−k rank(g−1))`.
* In (26) the value `m = ∞` is the regular character `δ_e`, which is `f_0` in source 2.
* For `q = 2` the group `F_2^*` is trivial, so `ε = 1`.
* Both sources state that the list (26) is complete, and credit the proof to Skudlarek. Source 2 also
  states that every normalized positive-definite class function is a convex combination of the list.
