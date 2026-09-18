---
rg: 2
id: boone-higman-iff-fp-just-infinite-hosts
kind: claim
title: Boone-Higman is equivalent to embedding every decidable finitely generated group in a finitely presented just-infinite group
distinct_from:
  boone-higman-iff-infinite-simple-inputs: that restricts the INPUTS to infinite computably presented simple groups and keeps the simple finitely presented target; this relaxes the TARGET from simple to just-infinite. Just-infinite targets may have arbitrarily many finite quotients and need not be virtually simple a priori.
  boone-higman-iff-simple-kazhdan-decidable-inputs: that restricts the inputs to decidable simple Kazhdan groups; this changes the host class, and it is what licenses normal subgroup theorems for lattices as host engines.
  boone-higman-conjecture: that asks for a finitely presented SIMPLE envelope; this proves that asking only for a finitely presented JUST-INFINITE envelope loses no strength.
  just-infinite-over-simple-subgroup-gives-fp-simple-host: that is the structure lemma consumed here; this is the resulting equivalence of conjectures.
---

**ESTABLISHED** through `boone-higman-iff-fp-just-infinite-hosts-proof`.

The following are equivalent.

1. (Boone–Higman) Every finitely generated group with solvable word problem embeds
   in a finitely presented simple group.
2. Every infinite finitely generated group with solvable word problem embeds in a
   finitely presented just-infinite group.
3. Every infinite finitely generated **simple** group with solvable word problem
   embeds in a finitely presented just-infinite group.

**Why this matters.** Every Boone–Higman route so far has aimed straight at a
simple target, or at a group with no finite quotients. Statement 2 aims at a
target that may have many finite quotients. The host only has to satisfy a
normal-subgroup dichotomy. Non-residual-finiteness, the one extra thing needed, is
imported automatically from the simple input. The known machines producing just-infinite groups are normal
subgroup theorems (Margulis, Burger–Mozes, Bader–Shalom). These produce lattices
that are finitely presented for free in many geometric settings. Before this
equivalence they were host engines only for inputs that happen to lie in lattices
already. The new route consuming this is
`boone-higman-via-bader-shalom-lattice-hosts`.

DERIVATION
boone-higman-iff-fp-just-infinite-hosts-proof
