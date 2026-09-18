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

**Also printed (added 2026-09-18, lane bh-openq-papers).** arXiv:2512.24266v3, *On the word
problem for just infinite groups*, Introduction, after its Theorem 2.1 (TeX l.123–128): "Does a
finitely generated group G have a decidable word problem if and only if G can be embedded
into finitely presented just infinite group?" It is posed there as a weakened version of the
Boone–Higman conjecture. The authors prove the "if" direction: finitely generated just
infinite groups with recursively enumerable presentations have decidable word problem. By
the equivalence above, the printed question is equivalent to Boone–Higman.

**Per-input refinement (lane remark).** For a single finitely generated input `G` that is not
residually finite, any finitely presented just-infinite host is virtually `S^k` with `S`
finitely presented, infinite and simple. By the trichotomy that paper quotes (l.64: branch,
or virtually `L^k` with `L` simple or hereditarily just infinite):
- branch groups and residually finite hereditarily just-infinite groups give residually
  finite hosts;
- a hereditarily just-infinite group that is not residually finite has its finite residual
  simple and of finite index;
- `S` is finitely presented as a retract of the finite-index subgroup `S^k`.

So the just-infinite relaxation gains room only for residually finite inputs.

**Lesson for general BH.** Relaxing "simple" to "just infinite" moves only the
residually finite inputs. Every input that is not residually finite still needs a
finitely presented simple group, up to finite index and finite powers.

DERIVATION
boone-higman-iff-fp-just-infinite-hosts-proof
