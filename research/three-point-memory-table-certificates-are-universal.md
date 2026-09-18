---
rg: 2
id: three-point-memory-table-certificates-are-universal
kind: claim
title: Every three-row forward table has a rule-free certificate in a class exactly when every group is locally embeddable into that class
distinct_from:
  strict-pairs-need-a-memory-with-five-elements: that decides every four-by-four table by finite quotients of its table group; this shows the same rule-free method cannot finish any bounded decoder size three or more over any class, since certifying all three-row tables is as strong as universal local embeddability.
  three-point-decoder-memory-injective-ca-are-surjective: that open claim bounds the decoder memory by three points; this shows every proof of it that uses only the table group and not the rules proves Gottschalk's conjecture outright.
  surjunctivity-is-axiomatized-by-rectangle-clauses: that reduces the conjecture to all strict data of all shapes, with rules; this keeps only the rule-free separation condition, only tables with three decoder points, and turns the condition into local embeddability for every class.
  table-groups-are-memory-holonomy-groups: that computes the table group of a fixed table as a holonomy group times a free group; this uses the ball tables of two-generator groups, whose table groups agree with the group on half the ball.
  gottschalk-surjunctivity-fixed-two-generator-tester: that fixes one host group whose surjunctivity decides the conjecture; this fixes the decoder shape and ranges over tables, and it holds for every class of groups, not only surjunctive ones.
  universal-local-approximation-fixed-two-generator-test-group: that tests a local approximation property on one fixed group; this tests it on the finite forward tables with three decoder points, through their table groups.
  large-window-table-groups-present-the-ambient-group: that takes the decoder window to be a large ball, so the table group is the whole finitely presented ambient group and finite images go blind over groups without finite quotients; this keeps the decoder at three points, lets only the encoder memory grow, and shows that certificates in any class for all such tables are equivalent to universal local embeddability into that class.
  amenable-decoder-memory-forces-surjectivity: that resolves every decoder memory generating an amenable group, which includes all two-point decoders; this shows two-row tables always have finite certificates and three-row tables have amenable certificates only if every group is locally embeddable into amenable groups, which is false.
artifacts:
  - experiments/gottschalk-three-row-certificate-universality-2026-09-17/ballcal.py
  - experiments/gottschalk-three-row-certificate-universality-2026-09-17/ballcal.out
---

**ESTABLISHED** by `three-point-memory-table-certificates-are-universal-proof`.

**Setting.** For finite label sets `S`, `M` containing `1`, and a rook-independent partition `T` of `S x M`, the table
group is `P(T) = < x_a (a in S u M), x_1 = 1 | x_s x_m = x_s' x_m' for (s, m) ~ (s', m') in T >`. The table `T` is
*realizable* when `T = T_f(G)` for some group `G` and distinct labels `S, M` in `G`. Let `C` be any class of groups
closed under isomorphism. A *`C`-certificate* for `T` is a homomorphism `psi: P(T) -> H` with `H` in `C` that is
injective on the set of reverse products `{x_m x_s : m in M, s in S}` of `P(T)`.

**Resolution.** If `C` consists of surjunctive groups, a realizable table with a `C`-certificate carries no strict
automaton pair, for any alphabet and any rules. With `C` the finite groups this is the resolution lemma behind
`strict-pairs-need-a-memory-with-five-elements`.

**Theorem.** For every `k >= 3` and every class `C` closed under isomorphism, the following are equivalent.

- (a) Every realizable table with `|S| = k` (and any finite `M`) has a `C`-certificate.
- (b) Every realizable table with `|M| = k` (and any finite `S`) has a `C`-certificate.
- (c) Every group is locally embeddable into `C`.

For `k = 2` every realizable table has a finite certificate, since `P(T)` is a cyclic group times a free group.
So `3` is the exact threshold.

The proof of (a) implies (c) uses *ball tables*. Let `K = <a, b>` be a group with `1, a, b` distinct, and take
`S = {1, a, b}`, `M = B_K(2r)` and `T = T_f(K)`. The edge relators give `x_(gh) = x_g x_h` in `P(T)` for `g, h` in
`B_K(r)`. A certificate is injective on the reverse products `x_m x_1 = x_m`, so it is a partial embedding of
`B_K(r)` into `C`.

**Consequences.**

1. **Gottschalk.** Take `C` = the surjunctive groups. Surjunctivity is closed under local embeddings, so (c) is
   Gottschalk's conjecture. The conjecture is therefore equivalent to: every realizable forward table with three
   decoder points has a surjunctive certificate. Any proof of
   `three-point-decoder-memory-injective-ca-are-surjective` through the table group alone proves the full conjecture.
   The same holds for any fixed bound `k >= 3` on either memory.
2. **Soficity.** Take `C` = the sofic groups. Every three-row table has a sofic certificate iff every group is sofic.
3. **Finite quotients fail, explicitly.** Take `K = BS(2,3) = <a, t | t^-1 a^2 t = a^3>`, `S = {1, a, t}` and
   `M = B_K(4)`. This is a realizable `3 x 147` table with 272 classes, and `P(T) = BS(2,3)`. With `u = t^-1 a t`,
   the reverse products `au` and `ua` are distinct in `P(T)`. They are equal in every group whose 2-generated
   subgroups are residually finite. So this table has no certificate in the finite groups, the linear groups or the
   residually finite groups.
4. **Amenable certificates fail.** Thompson's `V` is finitely presented, simple and nonamenable, so it is not
   locally embeddable into amenable groups. Hence some three-row table has no amenable certificate.

**What this kills.** It kills the census-and-separate program of `strict-pairs-need-a-memory-with-five-elements`
continued to decoder size three with larger encoder memories, for every target class. The finite-quotient version
dies at the explicit `3 x 147` table above, and at smaller gap tables where they exist. The version with any other
class `C` succeeds only if every group is locally embeddable into `C`. A resolution of a bounded-memory case beyond
two points must use the local rules `mu`, `nu`, or restrict the tables, for example by an amenability or growth
condition on the memory group.

The calibration script `ballcal.py` builds the `BS(2,3)` ball table by Britton reduction. It checks rook
independence and every edge relator used, checks that `au != ua`, and, as a sanity check, confirms `au = ua` under
every homomorphism to `S_n` for `n <= 5`.
