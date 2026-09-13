---
rg: 2
id: bms-sln-z-representations-agree-with-algebraic-ones-citation
kind: route
title: Bass-Milnor-Serre 1967, Theorem 16.2 with hypothesis (16.1) and Corollary 4.3, read from the Numdam scan
target: bms-sln-z-representations-agree-with-algebraic-ones
requires: []
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-part2-2026-09-13.md
---

H. Bass, J. Milnor, J.-P. Serre, *Solution of the congruence subgroup problem for SL_n (n >= 3) and
Sp_2n (n >= 2)*, Publ. Math. IHÉS 33 (1967), 59--137. Read from the Numdam scan
(`numdam.org/item/10.1007/BF02684586.pdf`), pages 95, 134 and 135.

§16, p. 134: *"Let G be a semi-simple, simply connected, algebraic group defined over Q, and let Γ be an
arithmetic subgroup of G_Q. [...] there is a canonical continuous homomorphism π : Γ̂ → G_(A^f), where
Γ̂ is the profinite completion of Γ. The main theorem of this section will invoke the following
hypothesis:"*

> (16.1) a) π(Γ̂) is open in G_(A^f). b) ker(π) is finite.

p. 135:

> **Theorem 16.2.** — With the hypothesis (16.1), suppose given a group homomorphism f : Γ → GL_n(Q).
> Then there is a homomorphism of algebraic groups F : G → GL_n, defined over Q, which coincides with f
> on a subgroup of finite index of Γ.

p. 95:

> **Corollary 4.3.** — Suppose that A is of arithmetic type and that n >= 3. [...] b) If A is not totally
> imaginary then C_q = {1} for all q.

Here `C_q = SL_n(A, q)/E_n(A, q)`. By point (i) of the Introduction (p. 60), *"Every subgroup of finite
index contains some E_q (q != 0), and E_q itself has finite index in Γ"*. For `A = Z` and `n = 3`, these
give that every finite-index subgroup of `SL_3(Z)` is a congruence subgroup, so `ker(π)` is trivial.
Part a) holds because `SL_3(Z)` maps onto every `SL_3(Z/N)`, so its closure in `Π_p SL_3(Z_p)` is
everything. A finite-index subgroup of `SL_3(Z)` is an arithmetic subgroup of `SL_3(Q)`.
