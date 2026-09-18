---
rg: 2
id: countable-char-zero-linear-from-countable-decidable-bh
kind: route
title: GL_n over a computable algebraic closure of Q(t_1, t_2, ...) has a solvable word problem
target: countable-char-zero-linear-groups-embed-in-fp-simple-groups
requires: [countable-decidable-groups-embed-in-fp-simple-groups]
---

**Fact (decidability).**
- Let `Ω` be an algebraic closure of `Q(t_1, t_2, …)`. The field
  `Q(t_1, t_2, …)` is computable: its elements are quotients of integer
  polynomials in finitely many variables, with decidable equality and arithmetic.
- A computable field has a computable algebraic closure (M. O. Rabin, *Computable
  algebra, general theory and theory of computable fields*, Trans. Amer. Math.
  Soc. 95 (1960), 341–360).
- So `Ω` may be taken computable. Then `GL_n(Ω)` has a computable enumeration of
  its elements, in which a word is the identity iff its exactly computed product
  is the identity matrix. So `GL_n(Ω)` is a countable group with a solvable word
  problem.

**Route.** By `countable-decidable-groups-embed-in-fp-simple-groups`, every
`GL_n(Ω)` embeds in a finitely presented simple group. By the equivalent form
recorded in `countable-char-zero-linear-groups-embed-in-fp-simple-groups`, every
countable subgroup of `GL_n(K)`, `K` of characteristic 0, lies in some
`GL_n(Ω)`. So the target follows. ∎
