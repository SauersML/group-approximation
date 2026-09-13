---
rg: 2
id: outer-extension-word-problem-is-kernel-bounded
kind: claim
title: An outer extension of a finitely generated centreless group embeds in its automorphism group, and its word problem costs at most one exponential over the kernel's
distinct_from:
  outer-extensions-of-fp-simple-groups-are-isolated: that proves such extensions are isolated when the kernel is finitely presented and simple; this bounds their word problem by the kernel's, for any finitely generated centreless kernel.
  complexity-bounded-host-classes-are-not-universal: that is the non-universality principle for host classes sharing one recursive bound; this supplies such a bound for all outer extensions of kernels from a bounded class.
  decidable-groups-embed-in-outer-extensions-of-fp-simple-groups: that is the open universality statement over outer extensions; this is the theorem that those extensions are no harder than their kernels, up to one exponential.
---

**ESTABLISHED** by `outer-extension-word-problem-kernel-bound-proof`
(elementary; it requires nothing).

**Statement.** Let `I` be a finitely generated group and `S ⊴ I` a finitely
generated normal subgroup with trivial centre, such that the conjugation
homomorphism `I/S → Out(S)` is injective.

- **(OE1)** Conjugation `I → Aut(S)` is injective.
- **(OE2)** Let `g` be recursive and non-decreasing. Suppose `S` has, for some
  finite generating set, word problem in `F(g)`: decidable in time
  `C*g(C*n) + C*n + C` for some constant `C` (notation of
  `uniform-wp-bound-excludes-bh-universal-targets`). Then `I` has word problem
  in `F(G)` with `G(n) = g(2^n) + 2^n`.

`G` depends only on `g`, not on `S`, `I` or the extension data.

**Consequence.** Fix a recursive non-decreasing `g`. All outer extensions of
all finitely generated centreless kernels with word problem in `F(g)` have
word problem in the one class `F(G)`. By
`complexity-bounded-host-classes-are-not-universal`, some two-generated group
with solvable word problem embeds in none of them. In particular no single
finitely presented simple group `S` carries every decidable input inside an
outer extension, split or not. The same holds for any class of such `S` sharing
one recursive bound.

**What this corrects.** Attempt 3 on
`every-decidable-group-embeds-in-an-isolated-group` said that non-split outer
extensions of one fixed `S` escape the complexity argument, because deciding
`q = 1` in the quotient is an innerness search in `S`. That search is the word
problem of the quotient `Q`. But the input must sit inside `I`, and (OE2) bounds
the word problem of `I` by that of `S`.

**Novelty.** None claimed. (OE1) is the centralizer argument of
`outer-extension-isolated-via-centralizer-argument`, and (OE2) is word
substitution followed by the kernel's word problem.
