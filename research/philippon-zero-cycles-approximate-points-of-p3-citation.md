---
rg: 2
id: philippon-zero-cycles-approximate-points-of-p3-citation
kind: route
title: P. Philippon, Approximations algebriques des points dans les espaces projectifs I, J. Number Theory 81 (2000) 234-253, Theoreme 1 (p. 236), read from the PDF
target: philippon-zero-cycles-approximate-points-of-p3
requires: []
---

**Source.** P. Philippon, *Approximations algebriques des points dans les
espaces projectifs I*, J. Number Theory 81 (2000) 234-253,
doi:10.1006/jnth.1999.2461. It was received 10 October 1996 and communicated by
M. Waldschmidt.
- **Retrieval, 2026-09-13.** ScienceDirect serves a bot page. The Elsevier
  open-archive copy came through CORE (output 82328610) as the Wayback snapshot
  `web.archive.org/web/20190419034132id_/https://core.ac.uk/download/pdf/82328610.pdf`,
  a 20-page PDF with md5 `7e60b0d073b610962cf81c8d6e65d0b9`.
- **How it was read.** Pages 234-238 were read as page images, and pages
  235-236 were cross-checked against ghostscript text extraction on MSI.

**Theoreme 1 (p. 236), verbatim** (only the accents are dropped):

> THEOREME 1. Soit `n in N*`, `c_n = 2^(n+4) n!` et `x in P_n(C)`, alors pour
> tous entiers `max(0, n-3) <= d <= n`, `H >= 1` et `Delta >= (4c_n)^(n-d+1)`,
> il existe un cycle `Z` de dimension `d`, irreductible et recursivement defini
> sur `Q` par des formes de degres `<= 2^(n-d) Delta` satisfaisant
> `d(Z) <= (c_n Delta)^(n-d)`,
> `h(Z) <= n log(n+1) c_n^(n-d) (H + Delta) Delta^(n-d-1)` et
>
> `log Dist(x, Z) <= -(4c_n)^(d-n) . (h(Z) Delta + d(Z)(H + log(Delta + 1))) Delta^d.`

**Specialisation.** The range `max(0, n-3) <= d` allows `d = 0` exactly when
`n <= 3`. Putting `d = 0` gives the statement of
[[philippon-zero-cycles-approximate-points-of-p3]].

**Constants (p. 237), verbatim.** "D'un point de vue numerique on notera que
`c_1 = 32`, `c_2 = 128`, `c_3 = 768`, ..."

**Definitions (pp. 235-236), paraphrased with the legible parts quoted.**
- **Height and degree.** "Soit `Z` une sous-variete projective de `P_n` de
  dimension `d`, definie sur `Q`, on note `d(Z)` son degre et `h(Z)` sa
  hauteur". For an eliminant form `g in Z[u^(1), ..., u^(d+1)]` of content 1,
  `d(Z) = d°g/(d+1)` and `h(Z) = m(g)`. Here
  `m(g) = integral over S_(n+1)(1)^(d+1) of log|g(u^(1), ..., u^(d+1))|`
  `d sigma_n(u^(1)) ^ ... ^ d sigma_n(u^(d+1)) + d°g . sum_(i=1..n) 1/(2i)`.
  "On a `h(Z) >= 0`."
- **Distance to a cycle.** `Dist(x, Z)` is defined for `||x|| = 1` from
  `m(d_x g)` and `m(g)`. Here `d_x: Z[u^(1), ..., u^(d+1)] -> Z[s^(1), ..., s^(d+1)]`
  is given by `d_x(u_j^(i)) = sum_(k=0..n) s_(j,k)^(i) x_k` with
  `s_(j,k)^(i) + s_(k,j)^(i) = 0`, following reference [11]. The operator
  glyph between `m(d_x g)` and `m(g)` is a slash in the page image and was
  dropped by the text extraction.
- **Extension to cycles.** "On etend les fonctions `d(.)`, `t(.)` et
  `log Dist(x, .)` aux cycles par linearite."
- **Points.** For `alpha in P_n(Qbar)`,
  "`Dist(x, alpha) = ||x ^ alpha|| / ||x|| . ||alpha||`".

**Also in the paper.**
- **Theoreme 3 (p. 237).** It is the same kind of statement inside a
  subvariety `V` of dimension `k in {0, 1, 2, 3}` defined over `Q`. The cycle
  satisfies `d(Z) <= d(V)(c_k Delta)^k`, and
  `log Dist(x, Z) <= -(4(4c_k)^(k+1))^(-1) (h(Z) Delta + d(Z) H)/d(V)`, for
  `Delta >= 2(4c_k)^(k+1)` and `H >= Delta ((h(V)/d(V)) + 3n log(n+2))`.
- **Abstract, verbatim.** "We establish approximation properties by algebraic
  points, of points in projective spaces of dimension ⩽3. ... The essential
  tool which enables us to reach dimension three is a refined effective lower
  bound for the Hilbert function of a prime ideal."
- **Codimension above 3 (p. 235).** "On notera que cette minoration n'est pas
  suffisante pour etendre nos resultats en codimension > 3."

**Not checked.** The proofs in Section 4 were not re-read. The theorem is
imported as published: peer-reviewed in JNT and cited 11 times per OpenAlex.
