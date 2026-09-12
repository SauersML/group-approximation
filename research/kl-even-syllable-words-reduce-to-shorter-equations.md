---
rg: 2
id: kl-even-syllable-words-reduce-to-shorter-equations
kind: claim
title: A word in the variable t^d reduces Kervaire--Laudenbach to a word of length divided by d, settling two coincidence-saturated length-six families
distinct_from:
  kl-length-six-one-coincidence-words-inject: that treats length-six words with exactly one same-sign coincidence by weights; this treats two families with at least three coincidences, involution loops included, by substituting a square root of the variable.
  kl-four-same-sign-corner-words-inject: that needs four light same-sign corners and fences coincidence-free words; this reaches words where every same-sign corner is heavy, which no weight test with involution loops can reach.
  kl-cyclic-cover-words-have-an-index-m-core: that passes to the index-m core of the degree kernel and keeps paired relators; this uses a word that already lies in G * <t^d>, so it needs no pairing at all.
---

**Reduction lemma.** Let `G` be any group, `d >= 1`, and `v in G * <z>` with
`deg_z(v) != 0`. Put `w = v(t^d) in G * <t>`. If
`G -> (G * <z>)/<<v>>` is injective, so is `G -> (G * <t>)/<<w>>`.

At length six this gives:

**Corollary (two length-six families).** Let `w` be a cyclically reduced word
of variable length six and class `++++--` after splitting powers:

```text
w = t a_1 t a_2 t a_3 t y t^(-1) n t^(-1) x,     a_i, n, x, y in G.
```

Suppose the same-sign labels satisfy either
- (E1) `a_1 = a_2 = a_3 = u` and `n = u^(-1)`, or
- (E2) `a_1 = a_3 = u` and `n = u^(-1)`, with `a_2` arbitrary.

Then `G -> (G * <t>)/<<w>>` is injective. Nothing is assumed about `x` or `y`:
both may be involutions.

In the four-corner terms, (E1) closes six trivial same-sign 2-cycles and (E2)
at least three, so both have `r <= 1` light corners. These are exactly the
cases in which the relative weight test is impossible with involution loops.

DERIVATION
kl-even-syllable-reduction-proof
