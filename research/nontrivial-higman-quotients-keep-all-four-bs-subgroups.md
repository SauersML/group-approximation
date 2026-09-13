---
rg: 2
id: nontrivial-higman-quotients-keep-all-four-bs-subgroups
kind: claim
title: In every nontrivial quotient of Higman's group the generators have infinite order and the four Baumslag--Solitar subgroups embed
distinct_from:
  nonsofic-subgroups-of-higman-group-have-free-edge-groups: that filters finitely generated nonsofic subgroups through the two amalgam splittings; this constrains normal subgroups, which meet the four Baumslag--Solitar subgroups trivially unless they are the whole group.
  linear-sterility-does-not-obstruct-division-embedding: that records that every finite-dimensional linear image of Higman's group is trivial; this says that every nontrivial image, linear or not, keeps all four Baumslag--Solitar subgroups.
artifacts:
  - research/artifacts/solve-higman-sofic-2026-09-13.md
---

**ESTABLISHED** by `higman-quotient-smallest-prime-proof` (elementary; no
novelty claimed).

**Statement.** Let

```text
H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >,   x^y = y^-1 x y,
```

let `N` be a normal subgroup of `H4` with `N != H4`, and put `Q = H4/N`.

1. The images of `a, b, c, d` in `Q` have infinite order.
2. `N` meets each of `<a,b>`, `<b,c>`, `<c,d>`, `<d,a>` trivially. Each of these
   is a copy of `BS(1,2)`, and it maps isomorphically onto its image in `Q`.

The presentation `a^b = a^2, b^c = b^2, c^d = c^2, d^a = d^2` defines the same
group with the cycle reversed, so the statement holds for it too.

**Corollaries.**
- **No finite quotients.** A nontrivial finite quotient would give generators of
  finite order. This recovers Higman's theorem.
- **Commuting opposite generators.** If `[a,c]` or `[b,d]` lies in `N`, then
  `N = H4`. Indeed `c^2 = c^4` follows from `b^a = b^2`, `c^b = c^2` and `ac = ca`
  (`almost-commuting-opposite-higman-generators-force-collapse` gives the metric
  version), so `c` has finite order.
- **Periodic laws.** No nontrivial quotient satisfies `x^n = 1` for any
  generator `x` and any `n >= 1`.
- **Sofic quotients of the Helfgott--Juschenko cover.** In the Kassabov--Kuperberg--Riley group
  `H_4(BS(1,2)) = H4 x| C_4`, a quotient contains `BS(1,2)` injectively exactly
  when the image of `H4` is nontrivial. This is the input to
  `base-two-exponential-permutations-iff-sofic-higman-quotient`.

**Where the argument stops.** The proof uses `m - 1 = 1` for the exponent `m = 2`.
For `H_(4,m)` with a prime `p | m - 1`, the smallest-prime step fails. This
matches Glebsky's finite `p`-quotients of those groups (Kassabov--Kuperberg--Riley
arXiv:1712.07191, Theorem `glebsky thm`, l.1252–1256 of their TeX).
