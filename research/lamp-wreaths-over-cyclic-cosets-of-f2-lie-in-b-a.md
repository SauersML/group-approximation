---
rg: 2
id: lamp-wreaths-over-cyclic-cosets-of-f2-lie-in-b-a
kind: claim
title: For a free basis element a of F_2, every B_A lamp group wreathed over F_2/<a> gives a group in B_A, so Z wr_(F_2/<a>) F_2 embeds in a finitely presented simple group
distinct_from:
  permutational-boone-higman-closed-under-wreath-products: that covers G-sets with finite point stabilizers; here the stabilizer <a> is infinite cyclic and F_2 has infinitely many double cosets <a>\F_2/<a>.
  wreaths-over-clopen-stabilizer-cosets-lie-in-b-a: that is the general lemma; this realizes <a> as the exact stabilizer of a clopen set for a ping-pong copy of F_2 in Thompson's V.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `lamp-wreaths-over-cyclic-cosets-of-f2-proof` (lane proof, elementary; not
independently reviewed; no priority claimed).

## Statement

Let `F = F_2` be free on `a, b`, and `X = F/⟨a⟩`. For every group `L` in `B_A` the
restricted permutational wreath product `L ≀_X F` lies in `B_A`; if `L` is finitely
generated it embeds in a finitely presented simple group. The same holds with `⟨a⟩`
replaced by `⟨c⟩` for any primitive element `c` (apply an automorphism of `F_2`).

This settles the first test case listed in `pbh-closed-under-decidable-permutational-wreaths`,
`Z wr_(F_2/⟨a⟩) F_2`. The same case was listed in the refuted
`pbh-closed-under-permutational-wreaths-with-infinite-stabilizers`, whose Attempt 2 does not
apply because `F_2` has infinitely many double cosets `⟨a⟩\F_2/⟨a⟩`.

## Mechanism

A ping-pong pair `α, β ∈ V` for which one clopen set `U` is fixed by `α` and pushed off
itself by every reduced word containing `β`. So `⟨α, β⟩ ≅ F_2` and `Stab_{⟨α,β⟩}(U) = ⟨α⟩`
exactly, and the clopen-orbit lemma applies with the host `V`.
