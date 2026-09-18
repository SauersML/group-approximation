---
rg: 2
id: houghton-h3-far-commutation-bounded-by-two-ray-pour-rewrite
kind: claim
title: "In H_3, commuting the top transposition past one pushed k steps down a ray costs at most 4 A_3(k-2) + O(k^3), where A_3 is the area of rewriting one pour into its two-ray word"
artifacts:
  - research/artifacts/zp-houghton-h3-far-commutation-via-pour-rewrite-2026-09-18.md
  - experiments/houghton-h3-2026-09-17/verify_far_commutation_via_pour_rewrite.py
distinct_from:
  houghton-far-commutation-has-quadratic-log-area-for-six-rays: that bounds the same family by k^2 log k for n >= 6 using two auxiliary rays; this is the three-ray case, with no auxiliary ray, bounded by one explicit pour rewrite instead of absolutely.
  houghton-far-transposition-commutation-is-superpolynomial: that asserts superpolynomial area for the family in some H_n; this is an unconditional upper comparison in H_3, so that assertion for n = 3 forces A_3 to be superpolynomial.
  houghton-four-ray-pour-route-change-bounded-by-h3-dehn: that bounds four-ray route changes by A_3 or δ_(H_3); this bounds three-ray far commutation and reroutes by the same A_3.
---

Let `n = 3` and let `P` be the finite presentation of `H_3` built by the recipe of
`research/artifacts/zp-houghton-pours-2026-09-17.md` §0. The recipe uses only Lee's
Theorem C and Lemma 3 of `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`,
both valid for `n >= 3`.

Define

```text
w_k    = τ_a D^b_a(k) τ_a^(-1) D^b_a(k)^(-1),   D^b_a(k) = λ_ab^k τ_a λ_ba^k,
A_3(m) = max over distinct rays x,y,z of Area_P( λ_xz^m λ_zy^m · (λ_xy^m ρ_y(m))^(-1) ),
```

where `λ_xy^m ρ_y(m)` is the two-ray word of length `<= m^3` of Lemma 1 of
`research/artifacts/zp-houghton-four-rays-via-h3-2026-09-18.md`. For `a = 1, b = 2`,
`w_k` is Lee's `[α, α^(g_1^(-k))]` up to `O(k)` substitutions. Then, for all `k >= 3`
and all distinct rays `a,b`,

```text
Area_P(w_k) <= 4 A_3(k-2) + 2k^3 + 14k,
```

and the reroute `D^a_b(j) -> D^c_b(j)` has area `<= 2A_3(j) + j^3 + 4j + 2`.

Consequences:

- `A_3(m) ≼ m^D` gives far-commutation area `≼ k^(max(D,3))` in `H_3`.
- By Remark 3.1 of the four-ray note, the same bound gives `δ_(H_4) ≼ x^(6+D)`.
- A superpolynomial lower bound for `w_k` in `H_3` forces `A_3` to be superpolynomial.
