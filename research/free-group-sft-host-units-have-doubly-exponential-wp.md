---
rg: 2
id: free-group-sft-host-units-have-doubly-exponential-wp
kind: claim
title: Finitely generated unit subgroups of SFT crossed products over free groups with finite coefficients have doubly exponential word problem
distinct_from:
  rational-homeomorphism-subgroups-have-exponential-wp: that bounds word problems of groups of rational homeomorphisms of Cantor space; this bounds word problems of unit groups of crossed-product algebras of tree SFTs, where elements are finite sums with coefficient tables rather than homeomorphisms.
  complexity-bounded-host-classes-are-not-universal: that turns any uniform recursive word-problem bound into non-universality; this supplies such a bound for one class of algebra hosts.
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
---

**ESTABLISHED (unreviewed).** Let `d >= 0`, let `X ⊆ A^(F_d)` be a nonempty subshift of finite type
and `k` a finite field. Every finitely generated subgroup `G` of the unit group of
`LC(X, k) ⋊ F_d` has, for every finite generating set, a word-problem algorithm running in time at
most `C * 2^(2^(C l))` on words of length `l`, with `C` depending on `G`, its generators, `X` and
`k`.

The key input is the local extension property of tree SFTs. After recoding to nearest-neighbour
form and pruning the alphabet, every locally legal pattern on a finite subtree extends to a point.
So the ball languages are decidable by local checking in time `2^(O(|B_M|))`.

DERIVATION
free-group-sft-host-units-have-doubly-exponential-wp-proof
