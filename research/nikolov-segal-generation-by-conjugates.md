---
rg: 2
id: nikolov-segal-generation-by-conjugates
kind: claim
title: In a finite group, generators modulo G_0 and G' give boundedly many generating conjugates, and a symmetric generating set gives [H,G] as a bounded product of the sets [H,y_i]
distinct_from:
  nikolov-segal-uniform-commutator-width: that is the commutator width of d-generator finite groups, from the 2007 Annals paper; this is the 2011 generation and twisted-commutator theorems, with conjugates of prescribed elements and commutators against prescribed generators.
---

**ESTABLISHED (literature import).** All groups are finite, `d(G)` is the minimal number of generators, and
`[x, g] = x^-1 g^-1 x g`, `[H, g] = { [x, g] : x in H }`, `X^(*f)` is the set of products of `f` elements of `X`.
`G_0` is the intersection of the normal subgroups `T` with `G/T` almost simple, equivalently of the
centralizers of the non-abelian simple chief factors. So `G_0 = G` when `G` has no almost simple quotient, for
example when `G` is soluble.

- **Theorem 1.1 (generation by conjugates).** Let `K <= G_0` be normal in `G` and suppose
  `G = K<y_1, ..., y_r> = G'<y_1, ..., y_r>`. Then there are `x_ij in K` with
  `G = < y_i^(x_ij) : i <= r, j <= f_0 >`, where `f_0 = f_0(r, d(G))`.
- **Theorem 1.2 (commutators against generators).** If `{y_1, ..., y_r}` is a symmetric generating set of `G`
  and `H` is normal in `G`, then `[H, G] = ( [H, y_1] ··· [H, y_r] )^(*f_1)`, where `f_1 = f_1(r, d(G))`.

Source: N. Nikolov and D. Segal, *Generators and commutators in finite groups; abstract quotients of compact
groups*, arXiv:1102.3037v6, Theorems 1.1 and 1.2 (page 3). The proofs use the classification of finite simple
groups; the soluble case of Theorem 1.1 is attributed there to Segal, *Closed subgroups of profinite groups*.

Source status: `nikolov-segal-generation-by-conjugates-citation`.
