---
rg: 2
id: bh-product-closure-via-boone-higman-conjecture
kind: route
title: A product of two finitely presented simple groups is finitely presented with solvable word problem, so the conjecture covers it
target: boone-higman-closed-under-finite-direct-products
requires:
  - boone-higman-conjecture
  - simple-envelope-forces-solvable-word-problem
artifacts:
  - research/artifacts/bh-product-closure-2026-09-12.md
---

Let G ≤ S_1 and H ≤ S_2 with S_1, S_2 finitely presented simple.
1. **Solvable word problem.** By `simple-envelope-forces-solvable-word-problem`
   (Kuznetsov), S_1 and S_2 have solvable word problem.
2. **The product.** S_1 x S_2 is finitely presented. Its word problem is solvable
   coordinatewise.
3. **Conjecture.** By `boone-higman-conjecture`, S_1 x S_2 embeds in a finitely
   presented simple group, and so does its subgroup G x H.

So closure under finite direct products is a consequence of the conjecture. It is
not a formal permanence property of the class, and its proof is open.
