---
rg: 2
id: sp2g-central-commutators-of-universal-lifts-are-torsion-proof
kind: route
title: Evaluate the Guichardet--Wigner homogeneous quasimorphism on a central commutator
target: sp2g-central-commutators-of-universal-lifts-are-torsion
requires: []
---

## Import (verbatim)

G. Ben Simon, M. Burger, T. Hartnick, A. Iozzi, A. Wienhard, *On weakly
maximal representations of surface groups*, arXiv:1305.2620v2 (12 Jan 2016).
The PDF was fetched on 2026-09-18 and pages 8--10 were read.

- **p. 8, (3.6)--(3.8).** "Endow G × Z with the group structure defined by
  the Borel map (g1,n1)(g2,n2) := (g1g2,n1 +n2 +c(g1,g2)) and let Gnκ denote
  the Borel group G×Z endowed with the unique compatible locally compact group
  topology". "Then f′nκ(g,m) = (1/n)m is a Borel quasimorphism such that df′nκ
  represents p∗nκ(κ). Its homogenization fnκ : Gnκ → R is a continuous
  homogeneous quasimorphism [13, Lemma 7.4] such that (3.7) [dfnκ] = p∗nκ(κ),
  and (3.8) fnκ(i(m)) = (1/n)m."
- **p. 10, §3.3.** "3.3. The Hermitian Case. Assume that G is of Hermitian
  type and almost simple." "If κ = nκb_G is any integer multiple represented by
  an integral cocycle, the topological central extension 0 → Z →i Gκ →pκ G → e
  is not trivial. Since π1(G) is isomorphic to Z modulo torsion, there is a
  unique connected central Z-extension Ĝ and, as a result, the connected
  component of the identity (Gκ)◦ is isomorphic to Ĝ. We denote by fĜ : Ĝ → R
  the continuous homogeneous quasimorphism corresponding to fκ under this
  isomorphism".

**Use.** `G = Sp_(2g)(R)` is almost simple of Hermitian type (Siegel upper half
space), and `pi_1(G) = pi_1(U(g)) = Z` (standard, not re-read), so `Ĝ = G^` is
the universal cover. Under `Ĝ = (Gκ)°`, `ker p = pi_1(G) = Z` sits in
`i(Z)`, and it is nonzero there, so by (3.8) `f = f_Ĝ` satisfies
`f(zeta) != 0` for a generator `zeta` of `ker p`.

## Elementary part

Let `f : G^ -> R` be a homogeneous quasimorphism with defect `D`.

1. *Additive on commuting pairs.* If `xy = yx`, then `(xy)^n = x^n y^n`, so
   `n |f(xy) - f(x) - f(y)| <= D` for all `n`, which gives `f(xy) = f(x) + f(y)`.
2. *Conjugation invariant.* `|f(h x^n h^-1) - f(h) - f(x^n) - f(h^-1)| <= 2D`
   and `f(h^-1) = -f(h)`, so `n |f(h x h^-1) - f(x)| <= 2D`.
3. *Center.* `ker p` is central (conjugation of a discrete normal subgroup
   of a connected group is constant). If `p(x)` is central in `G`, then
   `y -> x y x^-1 y^-1` is a continuous map from the connected `G^` to the
   discrete `ker p` that equals 1 at 1, so `x` is central. Hence
   `Z^ = p^-1(Z(G)) = p^-1({+-1})` (standard: `Z(Sp_(2g)(R)) = {+-1}`), and
   `[Z^ : ker p] = 2`. So `Z^` is abelian of rank 1. By 1, `f|Z^` is a
   homomorphism to `R`. It is nonzero on `zeta`, so its kernel is exactly
   `Tors(Z^)`. `Tors(Z^) cap ker p = 1`, so `Tors(Z^)` injects into
   `Z^/ker p = Z/2`.
4. *(CT1).* Let `w = [a,b] = a b a^-1 b^-1` be central. Then
   `a b a^-1 = w b` with `w` commuting with `b`. By 2 and 1,
   `f(b) = f(a b a^-1) = f(w) + f(b)`, so `f(w) = 0` and `w in Tors(Z^)`.
5. *Quotients.* For central `C`, the commutator in `G^/C` of the images of
   `a, b` is the image of `[a,b]`. If `p(a)`, `p(b)` commute, then
   `[a,b] in ker p cap Tors(Z^) = 1`. If `[aC, bC]` is central in `G^/C`,
   then `[a,b]` is central in `G^`. Put `x = [a,b]`. For every `y`,
   `[x,y] in C <= Z^`, so `y -> [p(x), y]` is a continuous map from the
   connected `G` into the discrete `{+-1}` that equals 1 at 1. So `p(x)` is
   central, and `x in Z^` by step 3. So `[a,b] in Tors(Z^)`, which is trivial in
   `G^/C` when `C >= Tors(Z^)`.
