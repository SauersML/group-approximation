---
rg: 2
id: germ-extension-base-nontrivial-characters-via-point-fixers
kind: claim
title: In a finite germ extension, a character lies in Sigma^m once its restrictions to the point-fixers Fix_B(M) with |M| <= m do
distinct_from:
  germ-extension-base-trivial-characters-lie-in-sigma: that treats characters vanishing on the base B by Morse theory with an equivariant height; this treats characters that are nonzero on every point-fixer of B, by Meinert's criterion on the same germ complex, and needs no height function.
---

**ESTABLISHED (proof in `germ-extension-base-nontrivial-characters-via-point-fixers-proof`; unreviewed).**

Let `G` be a finite germ extension of `B <= Homeo(X)`. Notation is that of
`germ-complex-and-bux-gonzalez-morse-inputs`, and `Fix_B(∅) = B`. Let `m >= 1` and assume:

1. `B` has finitely many orbits on `sing(G)^m`;
2. `Fix_B(M)` has type `F_m` for every `M ⊆ sing(G)` with `|M| <= m`;
3. `|(G)_p : (B)_p| < ∞` for every `p in sing(G)`.

Let `χ in Hom(G,R)`. Suppose that for every `M ⊆ sing(G)` with `|M| <= m`:

- `χ|_{Fix_B(M)} != 0`, and
- `[χ|_{Fix_B(M)}] in Σ^m(Fix_B(M))`.

Then `G` has type `F_m` and `[χ] in Σ^m(G)`.

**How it works.** `G` acts on the sublevel complex `K_{<=m}` of the Belk–Hyde–Matucci germ complex. The complex is
`(m−1)`-connected and the action is cocompact. Each cube stabilizer contains a conjugate of some `Fix_B(M)` with
`|M| <= m` as a subgroup of finite index. By finite-index and conjugation invariance, the hypothesis on the point-fixers
is exactly the stabilizer hypothesis of Meinert's criterion (`meinert-cocompact-action-criterion`).

**Scope.**

- The condition for `M = ∅` says `[χ|_B] in Σ^m(B)`. So the theorem transfers `Σ^m` from `B` to `G`, at the cost of
  also asking for the point-fixers.
- The two theorems split the characters. When `χ|_B = 0`, use `germ-extension-base-trivial-characters-lie-in-sigma`.
  When `χ` is nonzero on every `Fix_B(M)`, use this one. For Röver–Nekrashevych bases, every character of `B` is either
  zero or nonzero on every point-fixer (`rover-nekrashevych-polynomial-activity-tower-sigma-full-proof`, Lemma L). So
  the two cases cover everything.
- **Sanity check.** If `G = B`, then `sing(G) = ∅` and `K_{<=m}` is a point. The statement reduces to
  `[χ] in Σ^m(B) ⟹ [χ] in Σ^m(B)`.

## Attempts

- Proved; see the proof route. Used as case (a) of `germ-extension-point-fixer-sigma-heredity`.
