---
rg: 2
id: free-group-cantor-crossed-products-are-not-universal-hosts
kind: claim
title: Some decidable two-generated group algebra embeds in no finitely presented Cantor crossed product over a free group
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that is the general principle for any class of groups with a uniform recursive word-problem bound; this applies it to every finitely presented crossed product LC(X, k) ⋊ F_d, after proving that such hosts are SFT crossed products with doubly exponential unit word problems.
  boundary-crossed-product-is-a-leavitt-path-algebra: that identifies one simple finitely presented host over F_d; this shows that no host over any free group, whatever the space, contains every decidable group algebra.
  fixed-leavitt-hosts-cannot-be-universal-bh-containers: that excludes each single fixed Leavitt host; this excludes the whole family of crossed-product hosts over all free groups and all spaces at once.
  minimal-subshift-crossed-product-is-not-finitely-presented: that kills P = Z with a simple host through LEF; this kills every free P, simple or not, through word-problem complexity.
artifacts:
  - research/artifacts/fp-crossed-product-shape-free-group-kill-2026-09-17.md
  - research/artifacts/fjc-crossed-product-leavitt-hosts-2026-09-16.md
---

**ESTABLISHED (unreviewed).** There is a two-generated group `H` with solvable word problem such
that for no `d >= 0`, no nonempty compact totally disconnected `F_d`-space `X` and no finite field
`k` is there a finitely presented `k`-algebra `LC(X, k) ⋊ F_d` admitting a unital embedding
`k[H] -> LC(X, k) ⋊ F_d`.

**Consequence for the target.** In `decidable-group-algebras-have-fp-cantor-crossed-hosts`, the
acting group `P` can never be free, including `P = Z` and `P = 1`. This holds whatever the space
and regardless of simplicity or centre. The whole free-group family (Attempt 4 there) dies at one
step: the unital embedding of the hard input.

**Named invariant.** The local extension property of tree SFTs. It makes the ball languages of
every SFT over a free group decidable by local checking, which bounds all host unit word problems
uniformly in doubly exponential time. The obstruction is not dynamical. `LC(∂F_d, F_2) ⋊ F_d` is a
finitely presented simple host with centre `F_2` over a minimal, topologically free SFT.

DERIVATION
free-group-cantor-crossed-products-are-not-universal-hosts-proof
