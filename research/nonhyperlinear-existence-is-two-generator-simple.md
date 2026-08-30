---
rg: 2
id: nonhyperlinear-existence-is-two-generator-simple
kind: claim
title: Nonhyperlinearity exists iff it occurs in a two-generator simple group
distinct_from:
  countable-group-embeds-in-two-generator-simple-group: That is the classical embedding theorem with no approximation content; this combines it with locality and subgroup heredity of hyperlinearity to preserve nonhyperlinearity in the simple envelope.
  local-approximation-properties-are-marked-closed: That treats every local approximation property and also produces finitely presented covers; this selects a two-generator nonabelian simple overgroup and records the resulting one-word finite-window form.
  fp-simple-nonhyperlinearity-is-one-word-domination: That assumes a finitely presented simple group and obtains a whole-presentation modulus plus a linear character inequality; this existence reduction permits an arbitrary countable presentation and obtains finite relator windows, with no finite presentation or effective modulus.
---

For countable discrete groups, the following are equivalent:

1. a nonhyperlinear group exists;
2. a two-generator nonabelian simple nonhyperlinear group exists;
3. there are words `r_1,r_2,...,w in F(a,b)`, with `w` nontrivial in
   `S=<a,b | r_1,r_2,...>`, such that `S` is nonabelian simple and, for every
   `epsilon>0`, there are `N` and `delta>0` for which every finite-dimensional
   unitary pair `U=(U_a,U_b)` satisfies

   ```text
   max_(j<=N) ||r_j(U)-I||_2 < delta
   => ||w(U)-I||_2 < epsilon.                          (TGS1)
   ```

The relator enumeration in clause 3 need not be recursive.  Thus the bare
existence problem already reduces to two generators, simplicity, one
nontrivial word, and a non-effective finite-window normalized-HS collapse.
This is an existence compression, not an explicit witness: Schupp's envelope
does not provide a usable finite presentation or a computable collapse
modulus.
