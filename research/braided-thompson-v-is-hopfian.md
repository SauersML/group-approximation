---
rg: 2
id: braided-thompson-v-is-hopfian
kind: claim
title: The braided Thompson group bV is Hopfian
distinct_from:
  braided-thompson-group-bv-is-perfect: that claim computes the abelianization of bV; this one says every surjective endomorphism of bV is injective
---

Every surjective endomorphism of the Brin–Dehornoy braided Thompson group
`bV = V_br` is an automorphism.

This answers the first question of Zaremsky Problem 2.10 and the `V_br` half of
Question 4.7 of arXiv:1403.8132v2 affirmatively. It does not decide whether every
quotient of `bV` is finitely presented.

Status: complete argument in `research/artifacts/zp-braided-v-hopfian-2026-09-13.md`
(§§1–5). Reviewed PASS by z-verify-groups (d228d90964): see
`research/artifacts/zp-review-groups-2026-09-13-part2.md` §11. The novelty check is pending,
so do not describe this as a first answer yet.

## Attempts

- 2026-09-13 (z2-10-bv-hopfian): the argument has four steps.
  1. A surjective `phi` satisfies `phi^{-1}(P_br) = P_br`, by Corollary 2.8 of
     arXiv:1403.8132 and simplicity of `V`.
  2. `P_br` is residually nilpotent.
  3. The graded pieces of `P_br` are finitely generated `FS^op`-representations,
     which are noetherian by Sam–Snowden Corollary 8.1.3.
  4. The kernels of the iterates of the induced graded maps are `V`-invariant, so
     they stabilize, and each graded map is injective.

  The proof route `braided-thompson-v-is-hopfian-proof` lands with the lemma nodes.
