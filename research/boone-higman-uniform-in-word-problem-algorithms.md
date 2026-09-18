---
rg: 2
id: boone-higman-uniform-in-word-problem-algorithms
kind: claim
title: Boone-Higman envelopes can be computed uniformly from a finite presentation together with a total word-problem algorithm
distinct_from:
  boone-higman-conjecture: that asks for one envelope per input with no uniformity; this asks for one algorithm that produces envelopes from (presentation, decision procedure), and it implies the conjecture.
  fp-simple-envelopes-not-computable-from-presentations: that rules out computing envelopes from presentations (or acceptors) alone; this keeps a total decision procedure in the input, which that node's counterexamples lack.
  common-decidable-hosts-iff-uniform-word-problem: that proves, under Boone-Higman, uniform envelopes over every c.e. class with uniformly solvable word problem; this asks for uniformity over the non-c.e. family of all (presentation, decision procedure) pairs.
artifacts:
  - research/artifacts/gq-bh-bh-logic-logical-form.md
---

**OPEN.**

**Statement (UBH).** There is a partial computable function `F` with the following
property. Let `P` be a finite presentation, and let `e` be an index of a total
algorithm deciding the word problem of `G_P`. Then `F(P,e)` is defined and consists
of a finite presentation of a simple group `S` together with words `φ(x)` defining an
injective homomorphism `G_P -> S`.

## What is known

1. **UBH implies `boone-higman-conjecture`.** For finitely generated inputs, embed
   first in a finitely presented decidable group
   (`clapham-fp-embedding-preserves-word-problem`).
2. **The hosts must vary.** No single finitely generated group with solvable word
   problem contains every finitely presented group with solvable word problem. This
   is Boone--Rogers, via part 1 of `common-decidable-hosts-iff-uniform-word-problem`.
   So any `F` has unboundedly many hosts.
3. **Boone--Higman already gives UBH on every c.e. family.** Let `E` be a c.e. set of
   pairs `(P,e)` with every `e` total and correct. Then `{P : (P,e) ∈ E}` has
   uniformly solvable word problem: search `E` for a pair with first entry `P`, then
   run `e`. So under Boone--Higman, part 3 of
   `common-decidable-hosts-iff-uniform-word-problem` gives one finitely presented
   simple host with embeddings computable on `E`.
4. **Where UBH can fail.** The family of all valid pairs is `Π_2`, not c.e. So UBH
   can fail only through a non-c.e. spread of inputs. A refutation must show that
   every partial computable `F` fails on some valid pair, although each c.e. subfamily
   is handled correctly by some `F` if Boone--Higman holds.
5. **Consistency.** UBH does not contradict
   `fp-simple-envelopes-not-computable-from-presentations`. That node's
   counterexamples withhold exactly the total decision procedure, or the halting time
   it encodes, which UBH receives.
6. **Arithmetic form.** Boone--Higman is equivalent to a `Π_4` arithmetic sentence,
   and UBH is a `Σ_4` sentence. The computation is in the artifact. Both are
   therefore absolute between models of set theory with the same natural numbers, so
   forcing cannot make either independent.

A proof of Boone--Higman by an explicit construction that consumes the decision
procedure, such as those built from `boone-higman-thompson-simple-envelope`, would
normally give UBH as well. So UBH is the natural target for any constructive attack.
