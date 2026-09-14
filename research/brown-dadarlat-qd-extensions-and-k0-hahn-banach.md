---
rg: 2
id: brown-dadarlat-qd-extensions-and-k0-hahn-banach
kind: claim
title: Quasidiagonal extensions with UCT quotients are governed by the K_0-Hahn-Banach property (Brown-Dadarlat)
distinct_from:
  stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness: that glues quasidiagonal pieces through one-sided surjective pullbacks and never meets a K-theory boundary map; this is the literature theorem that controls genuine extensions through the index map and an embedding property of the ideal.
  stw99-problem-vii-blackadar-kirchberg: that is the full nuclear stably finite question; this is the imported extension theory, whose conclusions concern extensions of quasidiagonal algebras only.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**Established (literature).**  N. P. Brown and M. Dadarlat, *Extensions of
quasidiagonal C\*-algebras and K-theory*, arXiv:math/0008182, read 2026-09-11.

1. (Theorem 3.4)  Let `0 -> I -> E -> B -> 0` be exact with `E` separable, `I`
   quasidiagonal, and `B` nuclear, quasidiagonal and UCT.  If the boundary map
   `K_1(B) -> K_0(I)` is zero, then `E` is quasidiagonal.
2. (Definition 4.8)  A quasidiagonal `A` has the K_0-Hahn--Banach property if
   for every `x in K_0(A)` with `Zx cap K_0^+(A) = {0}` there are
   asymptotically multiplicative, asymptotically isometric c.c.p. maps
   `phi_n: A -> M_(k_n)` with `(phi_n)_*(x) = 0` for all large `n`.
3. (Theorem 4.11)  For the class of separable nuclear quasidiagonal algebras,
   the following are equivalent: every member has the QD extension property;
   every member has the K_0-embedding property; every member has the
   K_0-Hahn--Banach property; every singular `x` admits a QD embedding
   killing it; every singular `x` is the index of `[z] in K_1(C(T))` in some
   quasidiagonal extension `0 -> K tensor A -> E -> C(T) -> 0`.

Moutzouris (arXiv:2112.03224v3, Remark 2.5) records the consequence used in
this graph: if the ideal has the K_0-embedding property and the quotient is
separable, nuclear, quasidiagonal and UCT, the extension is quasidiagonal
exactly when it is stably finite (Spielberg's criterion
`d(K_1(B)) cap K_0^+(I) = {0}` for stable finiteness).
