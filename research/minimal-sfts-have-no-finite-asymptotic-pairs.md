---
rg: 2
id: minimal-sfts-have-no-finite-asymptotic-pairs
kind: claim
title: Over every infinite finitely generated group, a minimal subshift of finite type has no finite asymptotic pairs and is boundary-deterministic
distinct_from:
  minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs: that proves the same conclusion only over groups whose real group ring has no nonnegative zero divisor (and their finite-index overgroups), by a potential descent that fails for torsion; this proves it over every infinite finitely generated group, torsion included, by independent flips and the Lovász local lemma, so the (NZ) hypothesis and the persistent-torsion loophole recorded there are removed.
  fp-v-times-subshift-full-groups-force-connected-differences: that derives no finite asymptotic pairs from finite presentation of the V-product full group; this derives it from minimality and finite type alone, so part 2 there has no content beyond this claim.
  fp-minimal-crossed-products-have-no-homoclinic-pairs: that derives the absence of homoclinic pairs from finite presentation of a crossed product; this derives it from minimality and finite type, with no algebra.
  v-times-minimal-free-sft-alternating-full-groups-are-fp: that is the open finiteness premise P2; this shows that no counterexample to P2 can come from a finite asymptotic pair, over any acting group.
---

**ESTABLISHED (unreviewed).** Proof: `minimal-sfts-have-no-finite-asymptotic-pairs-proof`.
The proof uses only the symmetric Lovász local lemma (Erdős–Lovász 1975), a standard fact of
finite probability, and compactness. No novelty is claimed. Over `Z^d` the conclusion is also
implied by the Quas–Trow zero-entropy theorem (context only, not re-read).

## Setting

- `Λ` is an infinite group with a finite symmetric generating set, word length `|.|`, balls
  `B_n = {g : |g| <= n}` and `β(n) = |B_n|`. The metric is `d(g, h) = |g^(-1)h|`.
- `A` is a finite alphabet and `(g.x)(h) = x(g^(-1)h)` on `A^Λ`.
- `X ⊆ A^Λ` is a nonempty subshift of finite type: there are a finite symmetric `B ∋ 1` and
  allowed patterns `W ⊆ A^B` with `x ∈ X` iff `(k^(-1).x)|_B ∈ W` for every `k ∈ Λ`.
- `Δ(x, y) = {h : x(h) ≠ y(h)}`. A *finite asymptotic pair* is `x ≠ x'` in `X` with
  `Δ(x, x')` finite.

## Theorem

1. **No finite asymptotic pairs.** If `X` is minimal, no two distinct points of `X` differ on a
   finite set.
2. **Boundary determinism.** If `X` is minimal, then for every finite `F ⊆ Λ` the restriction
   `L_F(X) -> L_(∂F)(X)` is injective, where `∂F = {p ∈ F : pB^2 ⊄ F}`. So
   `|L_F(X)| <= |A|^|∂F|`, and over `Z^d`, `log |L_([0,N]^d)(X)| = O(N^(d-1))`.

Part 2 follows from part 1 by part 3 of `minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs`,
which proves the equivalence of (i) no finite asymptotic pair and (ii) injectivity of restriction
to `∂F`, for every SFT over every group.

**The hypothesis "infinite" is needed.** Over a finite group, a single orbit of two distinct
points is a minimal SFT, and its two points differ on a finite set. The proof uses infiniteness
exactly once: `β(n) -> ∞`.

## Consequences

- **The torsion loophole is closed.** `minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs`
  left open acting groups with a nonnegative zero divisor that survives in every finite-index
  subgroup, and named its descent invariant `a * ν_b = 0` as what such a counterexample must
  carry. Over every infinite finitely generated group that invariant is idle: minimality and
  finite type already exclude the pair.
- **For P2** (`v-times-minimal-free-sft-alternating-full-groups-are-fp`). The refutation class
  "a minimal free SFT with a finite asymptotic pair, fed to
  `fp-v-times-subshift-full-groups-force-connected-differences`" is empty over every infinite
  finitely presented `Λ`. Parts 2 and 3 of that theorem, and of
  `fp-crossed-products-force-connected-differences`, are automatic for minimal SFTs. What
  remains of those necessary conditions is part 1: coarse connectivity of infinite difference
  sets.
