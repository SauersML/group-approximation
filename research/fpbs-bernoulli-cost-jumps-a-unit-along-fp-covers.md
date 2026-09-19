---
rg: 2
id: fpbs-bernoulli-cost-jumps-a-unit-along-fp-covers
kind: claim
title: Finitely presented covers of cost one and beta_1 zero converge to a group of fixed price two, so cost-Betti cannot pass from fp to fg groups by semicontinuity along arbitrary covers
distinct_from:
  fpbs-bernoulli-cost-usc-on-marked-groups: that proves limsup C(b_(G_n)) <= C(b_G); this shows the inequality can be strict by a full unit along finitely presented covers
  fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap: that locates a possible cost jump between a Bernoulli shift and its ultraproduct for one group; this is an explicit jump across a sequence of different groups, where every term and the limit satisfy cost-Betti
  burton-kechris-cost-usc-and-maximum-action: that is semicontinuity in the weak topology for one group; this is a failure of lower semicontinuity in the marked-group topology
artifacts:
  - research/artifacts/fpbs-marked-group-cost-limits-2026-09-19.md
---

**ESTABLISHED.** Write `a_i = t^i a t^-i` and `r_R = [a, a_(R+1)]`. Let

    H   = (Z wr Z) * Z = < a,t,c | [a, a_k] (k >= 1) >,
    E_R = < a,t,c | [a, a_k] (1 <= k <= R), [r_R, c] >.

Then the following hold.

- `E_R` is finitely presented, surjects onto `H`, and `E_R -> H` in the space of 3-marked groups.
- `C(b_(E_R)) = 1` and `beta_1(E_R) = 0`.
- `C(b_H) = 2` and `beta_1(H) = 1`.

Here is why. `A_R = < a,t | [a, a_k], k <= R >` is the HNN extension of `Z^(R+1)` over `Z^R`. By Britton's lemma,
`r_R` is cyclically reduced of `t`-length 4, so `E_R = A_R *_Z Z^2`. Gaboriau's bounds over infinite amenable edge
groups then give cost `1`.

Consequences:

- Bernoulli cost and `beta_1` are not lower semicontinuous along finitely presented covers. They jump by a unit even
  though every term and the limit satisfy `C = 1 + beta_1`.
- Every finite certificate of cost below `2` on `E_R` has radius beyond the agreement radius of `E_R` and `H`.

**Obstruction.** This kills every transfer of cost-Betti or fixed price from finitely presented to finitely generated
groups that passes to the limit along arbitrary finitely presented covers. The invariant is the relator-length profile:
level `R` uses a relator of length about `8R`. Every such argument dies at the limit step `C(b_G) <= liminf C(b_(G_n))`.

Length-canonical covers `F/<<N cap B_R>>` of `H` do not jump. Artifact, Sections 2 and 3 (C0).
