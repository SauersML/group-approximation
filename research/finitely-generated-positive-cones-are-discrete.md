---
rg: 2
id: finitely-generated-positive-cones-are-discrete
kind: claim
title: A left order whose positive cone is a finitely generated semigroup is discrete, its least positive element e is the least generator, ⟨e⟩ is convex, e admits no Baumslag–Solitar self-conjugacy, every element normalizing the cone commutes with e, and the distortion of ⟨e⟩ bounds the positive distortion from below
distinct_from:
  finitely-generated-positive-cones-give-rigid-seeds: that puts every finitely generated positive cone into 𝒞; this is the structure of such cones (discreteness, the least element, no BS self-conjugacy), which also makes the dense case recorded there vacuous.
  isolated-order-word-problems-are-bounded-by-positive-distortion: that bounds the word problem above by the positive distortion D_P and the Dehn function; this bounds D_P below by the distortion of the least positive element, and rules out the Baumslag–Solitar mechanism for making it large.
  dehornoy-o-type-reversing-is-polynomial: that is Dehornoy's printed open question on the complexity of subword reversing for monoids of O-type; this proves structure that any answer must respect.
---

**ESTABLISHED** by `finitely-generated-positive-cones-are-discrete-proof` (lane bh-emitter-a, 2026-09-19;
elementary; not reviewed). No priority is claimed: item 1 is a one-line observation and is probably folklore.

## Setting

`G` is a group with a left order `<` whose positive cone `P` is generated as a semigroup by a finite set `S⁺`. Put
`M = P ∪ {1}`. By Dehornoy (arXiv:1204.3211, Lemma 1.3 and Proposition 1.4, read 2026-09-19), these are exactly
the groups of right fractions of finitely generated monoids of **O-type**: cancellative, with no nontrivial
invertible element, and with left and right divisibility both linear orders. Left divisibility in `M` is the
order `<` restricted to `M`.

Notation:
- `ℓ_+(g)` is the length of a shortest `S⁺`-word for `g ∈ P`;
- `K_e = max{k ≥ 1 : e^k ∈ S⁺}`;
- `Dist_e(n) = max{N : |e^N| ≤ n}` in the word metric of `S⁺ ∪ (S⁺)^{-1}`.

## Statement

1. **Discreteness.** `e := min S⁺` is the least element of `P`. So `x e` is the successor of `x` for every `x`, and
   `[x, x e^a] = {x, x e, …, x e^a}` for every `a ≥ 0`. The least element of `S⁺` for the right-invariant order
   (`g <′ h` iff `h g^{-1} ∈ P`) is likewise least in `P` for `<′`.
2. **Convexity.** `⟨e⟩` is a convex subgroup.
3. **No Baumslag–Solitar self-conjugacy.** If `g^{-1} e^a g = e^b` with `a, b ≠ 0`, then `|a| = |b|`.
4. **Cone normalizers centralize `e`.** If `g^{-1} P g = P`, then `g e = e g`. This covers every quasi-central
   element `Δ` of `M` in Dehornoy's sense (`sΔ = Δφ(s)` with `φ(s) ∈ M` for all `s ∈ S⁺`), so `φ(e) = e`.
5. **Lower bound on positive distortion.** `ℓ_+(e^N) ≥ N / K_e`. So
   `D_P(n) ≥ Dist_e(n) / K_e`, with `D_P` as in `isolated-order-word-problems-are-bounded-by-positive-distortion`.

## Consequences

- **No dense order has a finitely generated cone.** The dense case of
  `finitely-generated-positive-cones-give-rigid-seeds`, instance 2 of `order-seeds-are-rigid-relative-seeds` and
  the example in `order-seeds-transfer-computable-orders` were vacuous. Their discrete statements are the real
  ones, and those nodes are corrected accordingly. Question (O) concerns discrete isolated orders.
- **Consistency checks.** Ito's partially central cyclic amalgams (arXiv:1107.0545, Theorem 1.1 (iv) and (vi),
  read 2026-09-18) have a least positive element `x_1`, and `⟨x_1⟩` is their only proper nontrivial convex
  subgroup. That agrees with items 1 and 2.
- **Dehornoy's Example 10.10 explained.** The presentation `(a, b ; a = bab^{r+1})` of `BS(r+1, −1)` has
  exponential reversing complexity, and Dehornoy notes that its monoid is not of left-O-type.
  - Item 3 gives a one-line reason. In an O-type monoid `b < a` would make `b` the least positive element, but
    `a^{-1} b a = b^{-(r+1)}` is a Baumslag–Solitar self-conjugacy with `r + 1 ≠ 1`.
- **CAP on this class.**
  - Items 3–5 remove the natural mechanism for exponential positive distortion: conjugation that multiplies a
    minimal positive letter. That is exactly Dehornoy's duplicating quasi-central mechanism.
  - Any CAP counterexample among groups with finitely generated cones must get large `D_P` another way:
    distortion of `e` without BS relations (nilpotent- or Sol-type), or distortion of non-minimal positive
    elements.
  - The bridge to Dehornoy's Question 10.11 is recorded in `dehornoy-o-type-reversing-is-polynomial`.

## Lesson for general BH

A finitely generated positive cone forces a discrete order with a convex, conjugation-rigid bottom `⟨e⟩`.
- **What that rules out.** It kills the Baumslag–Solitar route to hardness at its root, and it explains Dehornoy's
  observation that his exponential reversing examples are never of O-type.
- **Where hardness must live.** In an isolated order it has to live strictly above the bottom convex subgroup.
- **The CAP question for these groups.** It is now Dehornoy's printed Question 10.11, with the least positive
  element as the first thing any counterexample must get past.
