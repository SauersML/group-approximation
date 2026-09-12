---
rg: 2
id: rf-lamp-wreaths-over-surjunctive-bases-are-surjunctive
kind: claim
title: Permutational wreath products with residually finite lamps over surjunctive groups are surjunctive
distinct_from:
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that is the linear theorem, stable finiteness of k[A wr_X G] from stable finiteness of k[G] over every field; this is full nonlinear surjunctivity from surjunctivity of G, proved through coset strata rather than matrix corners.
  surjunctive-guard-subgroups-force-surjectivity: that proves surjectivity of automata over an arbitrary group preserving unions of cosets of one surjunctive guard subgroup; this proves surjectivity of every injective automaton over one class of groups, with no hypothesis on the automaton.
artifacts:
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

Let `G` be any group, `X` any left `G`-set and `A` a residually finite group.
Put `W = A wr_X G = (direct_sum_X A) semidirect G`, with the permutation action
and no internal automorphism twists. Then

```text
W is surjunctive   <=>   G is surjunctive.
```

No finite generation, stabilizer condition, transitivity or faithfulness of
the action is assumed.

**Proof outline.** Full proof in the linked artifact.

1. **Transplant.** Transplant an injective automaton `tau` over `W` to the
   right coset spaces `H_(S,A_0)\W ~= (A/A_0)^S x G` of the subgroups fixing
   the lamp classes at finitely many marked sites `S`. The transplants stay
   injective, and pullbacks along these spaces separate every finite subset
   of `W`.
2. **Strata.** On such a space the rule is uniform except on the strata
   `Z_s`, `s in S`, where a lamp read by the memory sits at `s`. Each `Z_s` is
   a finite union of right cosets of the point stabilizer `G_s`.
3. **Peeling.** Compose with slicewise inverses of the lower-level transplants,
   in order of cardinality. The composite becomes the identity off a finite
   union of right cosets of `G_S = intersection_(s in S) G_s`.
4. **Coset-region lemma.** A finite-memory injection that is the identity
   off finitely many right cosets of a surjunctive subgroup `K`, with
   `K`-invariant rules there, is a cellular automaton over `K` with boundary
   labels, hence bijective. Every `G_U` is a subgroup of `G`, hence
   surjunctive.

The main consumer is `kun-thom-nonsofic-wreaths-are-surjunctive`. Finite
iterations with residually finite lamps over a surjunctive base are also
surjunctive.

This does not prove Gottschalk's conjecture. It does not treat the binary
Leavitt unit group, amalgams such as Kun--Thom group doubles, twisted lamp
actions, or non-residually-finite lamps.
