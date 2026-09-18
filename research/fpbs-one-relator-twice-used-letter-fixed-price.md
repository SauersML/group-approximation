---
rg: 2
id: fpbs-one-relator-twice-used-letter-fixed-price
kind: claim
title: One-relator groups in which some generator is used exactly twice have Morse deficit zero and fixed price |S|-1/m
artifacts:
  - research/artifacts/fpbs/docs/dual-forest-morse-matching-one-relator.md
distinct_from:
  one-relator-group-cost-equals-first-l2-betti-plus-one: that computes the infimum cost of every infinite one-relator group from one special action and does not bound the Bernoulli cost; this bounds the Bernoulli cost for a subclass and so gives fixed price there
  fpbs-morse-deficit-vanishes-for-full-presentations: that asserts vanishing Morse deficit for every finitely generated group; this proves it, with a single relator and no deep words, for one-relator groups with a twice-used letter
  fpbs-bernoulli-morse-collapse-criterion: that proves the criterion and records one-relator fixed price as open; this supplies a matching attaining the proper-power ceiling for a subclass
---

**ESTABLISHED.** Let `S` be finite, `m >= 1`, and `w` a cyclically reduced
word in `S^{+-1}` that is not a proper power. Suppose some `s in S` occurs
exactly twice in `w`, counting `s` and `s^{-1}`. Put `Gamma = <S | w^m>`.
Then:

- `Gamma` is infinite;
- the single-relator list `R = {w^m}` has Morse deficit `m(R) = 0`, so (Q1)
  of the criterion artifact holds;
- the Bernoulli action has cost `|S| - 1/m = 1 + beta_1^(2)(Gamma)`;
- every essentially free p.m.p. action of `Gamma` has cost `|S| - 1/m`, so
  `Gamma` has fixed price.

The other letters of `w` may occur any number of times. Examples beyond the
known surface, `Z^2`, Baumslag-Solitar and `<a,b | [a,b]^m>` cases are
`<a,b,c | (a b a^{-1} c^2 b c^{-1})^m>` and `<a,b,c | (a b a c b^{-1} c^2)^m>`.
Novelty was checked only against this graph and the Poulin-Wróbel source
record, not against the wider literature.

The matching is a dual-forest Morse matching. Each `s`-edge lies on exactly
two boundary cycles. Build the dual graph on cycles, whose components are
infinite by the Freiheitssatz. Take the BFS forest toward sparse iid markers
and match each non-root cycle to the `s`-edge leading to its parent. Mass
transport makes the trees finite, which is (M3).
