---
rg: 2
id: wreaths-over-undecidable-cosets-have-unsolvable-wp
kind: claim
title: A wreath product L wr_(G/H) G with L nontrivial has solvable word problem only if H has decidable membership in G, so Z wr_(F_k/N) F_k lies outside B_A for suitable normal N
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that asserts closure of B_A under wreath products over every countable G-set; this is the countermodel that refutes that assertion as stated.
  simple-envelope-forces-solvable-word-problem: that is the general word-problem obstruction for subgroups of finitely presented simple groups; this applies it to wreath products over coset spaces with undecidable membership.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `wreaths-over-undecidable-cosets-wp-proof` (lane proof, elementary; not
independently reviewed; no priority claimed, as the reduction is standard).

## Statement

1. **Reduction.** Let `G` be finitely generated, `H ≤ G`, and `L` a nontrivial finitely
   generated group. If the restricted permutational wreath product `L ≀_{G/H} G` has
   solvable word problem, then membership in `H` is decidable: given a word `u` in the
   generators of `G`, one can decide whether `u ∈ H`.
2. **Countermodel.**
   - Let `B = ⟨x_1, …, x_k | R⟩` be a finitely presented group with unsolvable word problem
     (`novikov-boone-fp-group-undecidable-word-problem`).
   - Let `N` be the kernel of `F_k ->> B`, and `X = F_k/N`.
   - Then `Z ≀_X F_k` is finitely generated, with unsolvable word problem.
   - So it lies in no finitely presented simple group
     (`simple-envelope-forces-solvable-word-problem`), and not in `B_A`
     (`type-a-action-gives-boone-higman-for-subgroups`).
   - Since `Z` and `F_k` both lie in `B_A` (both embed in Thompson's `V`, which has a type
     (A) clopen action), the claim `pbh-closed-under-permutational-wreaths-with-infinite-stabilizers`
     is false as stated.

## Corrected form

The hypothesis the refuted claim lacks is decidability of stabilizer membership. The
corrected open question is `pbh-closed-under-wreaths-over-decidable-coset-spaces`.
