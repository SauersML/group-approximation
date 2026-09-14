---
rg: 2
id: proper-self-conjugate-subgroups-force-free-subsemigroups
kind: claim
title: A subgroup properly containing one of its own conjugates yields a free subsemigroup of rank two
---

**Statement.** Let `G` be a group.

0. **Length criterion.** Let `x, y in G`. If distinct positive words of the same length in
   `x, y` always give distinct elements, then `x, y` freely generate a free subsemigroup.
1. **Main claim.** Suppose `H <= G` and `t in G` satisfy `t H t^{-1} ⊊ H`, and pick
   `a in H \ t H t^{-1}`. Then `t` and `a t` freely generate a free subsemigroup of rank 2.
2. **Growth.** If `G` is finitely generated and has such a pair `(H, t)`, then `G` has
   exponential growth. So a finitely generated group of subexponential growth has no subgroup
   `H` with `t H t^{-1} ⊊ H` for any `t`.
3. **Ascending HNN extensions.** If `theta: H -> H` is injective and not surjective, the
   ascending HNN extension `<H, t | t h t^{-1} = theta(h), h in H>` contains a free subsemigroup
   of rank 2, and has exponential growth when finitely generated.

Elementary; no novelty is claimed.
