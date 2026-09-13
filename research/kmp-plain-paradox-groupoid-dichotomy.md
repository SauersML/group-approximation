---
rg: 2
id: kmp-plain-paradox-groupoid-dichotomy
kind: claim
title: Simple topologically free groupoid C*-algebras whose type semigroup has plain paradoxes are stably finite or purely infinite, and stable finiteness is exactly a state (Kwasniewski-Meyer-Prasad)
---

**Import (Kwasniewski--Meyer--Prasad, arXiv:2502.17190v3, 28 Jul 2026).**

A preordered abelian monoid `S` has *plain paradoxes* if `(n+1)x <= nx`
implies `2x <= x` for all `x in S` and `n >= 1` (their Definition 2.18).
The monoid `{0, 1, infinity}` with `1 + 1 = infinity` fails it (their
Example 2.22).

* **Theorem 6.5.**  If `C*_r(G, L)` is simple, then `C*_r(G, L)` is stably
  finite iff the type semigroup `S_B(G)` admits a nontrivial state, iff there
  is a nontrivial regular `G`-invariant Borel measure on `X`.
* **Corollary 6.8.**  Let `G` be minimal and topologically free, with an
  inverse semigroup basis `B` of precompact sigma-compact bisections
  trivialising `L`, and assume no nonzero positive `f` has meagre
  `{x : E(f)(x) != 0}`.  If `S_B(G)` has plain paradoxes, then `C*_r(G, L)` is
  simple and either purely infinite or stably finite.
* **Remark 6.6.**  For ample `G` with `B` the compact open bisections, one may
  use the type semigroup `S(G)`.

**Consequence for Cantor crossed products.**  Let `Gamma` act minimally and
topologically freely on the Cantor space `X`.  The transformation groupoid is
Hausdorff, so `E(f)` is continuous and a nonzero `E(f)` has an open, hence
non-meagre, support; the meagre hypothesis holds.  So if `C(X) rtimes_r Gamma`
is neither stably finite nor purely infinite, then `S(X, Gamma)` has no
nontrivial state and fails plain paradoxes.  Candidates from
`topologically-free-minimal-cantor-action-with-finite-clopen-type` with the
Ortega--Perera--Rordam monoid have exactly this monoid shape.  KMP give no
converse without almost unperforation (their Theorem B(4)).
