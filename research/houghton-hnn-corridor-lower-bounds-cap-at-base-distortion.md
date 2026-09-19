---
rg: 2
id: houghton-hnn-corridor-lower-bounds-cap-at-base-distortion
kind: claim
title: "Corridor lower bounds for the Dehn function of H_n over the one-ray stabilizer H_(n-1) are capped by x times the distortion of H_(n-1): exactly x^3 for n = 3, at most x^2 log x for n >= 4"
distinct_from:
  houghton-cohomological-dehn-lower-bounds-cap-at-quadratic: that caps cocycle and central-extension certificates at x^2; this caps a different certificate class (t-corridor costs in an HNN presentation), whose cap is x^3 at n = 3, so the two classes are not comparable.
  houghton-group-h3-has-at-least-cubic-dehn-function: that proves x^3 is a lower bound for H_3 by one corridor-cost certificate; this proves no corridor-cost certificate of that kind can give more than x^3, and none can give more than x^2 log x for n >= 4.
  houghton-groups-have-quadratic-dehn-function: that is the (refuted at n = 3) assertion about the Dehn function itself; this is a statement about what one proof method can certify.
---

Fix `n >= 3`. Let `B ≤ H_n` be the pointwise stabilizer of ray `n`, so
`B ≅ H_(n-1)`, and let `t = λ_(1,n)`. Then `t B t^(-1) ⊆ B`, and `H_n` is
the ascending HNN extension `B *_φ` with `φ(b) = t b t^(-1)`.

**HNN-shaped presentations.** Call a finite presentation
`P = <S_B, t | R_0 ∪ R_1>` of `H_n` *HNN-shaped* if:

- `S_B` is a finite generating set of `B`;
- the relators in `R_0` contain no `t^(±1)`;
- each relator in `R_1` contains exactly one `t` and one `t^(-1)`, and its two
  sides (the subwords between them) are words in `S_B^(±1)`;
- `R_1` contains, for every `s ∈ S_B`, a relator `t s t^(-1) W_s^(-1)` with
  `W_s` a word in `S_B^(±1)`.

Such presentations exist for every `n >= 3`.

**Corridor costs.** In a van Kampen diagram over `P` for a null-homotopic word
`w`, the `t`-corridors pair the `t`-letters of `w`. A **corridor cost** for
`P` is a function `c : B → [0, ∞)` such that, in every van Kampen diagram over
`P` of every null-homotopic word `w`, every corridor joining letters `i < j`
of `w` has at least `c(w(i,j))` cells. Here `w(i,j) = w_(i+1) … w_(j-1)` is
the arc between the paired letters, and it represents an element of `B`. The
associated **corridor lower bound** is

`Area_P(w) >= min over diagrams D of Σ_(pairs (i,j) of D) c(w(i,j))`.

The cubic lower bound for `H_3`
(`houghton-group-h3-has-at-least-cubic-dehn-function`) is a corridor lower
bound, with `c = inv`.

**Claim.** Let `P` be HNN-shaped, and let `M` be the maximal length of a side
of a relator in `R_1`.

1. **Corridors measure base length.** `b ↦ |b|_(S_B) / M` is a corridor cost,
   and every corridor cost `c` satisfies `c(b) <= |b|_(S_B)` for all `b ∈ B`.
2. **Cap.** For every null-homotopic `w` of length `ℓ`, every diagram `D` and
   every corridor cost `c`,

   `Σ_(pairs (i,j) of D) c(w(i,j)) <= (ℓ/2) · Dist_P(ℓ)`,

   where `Dist_P(ℓ) = max { |b|_(S_B) : b ∈ B, |b|_(S_B ∪ {t}) <= ℓ }` is
   the distortion of `B ≅ H_(n-1)` in `H_n`.
3. **Consequences.**
   - `n = 3`: every corridor lower bound is `≼ x^3`. This is sharp: for the
     words `w_m` of the cubic proof, every diagram over every HNN-shaped
     presentation has corridor cost `>= c_P m^3` for a constant `c_P > 0`
     and the corridor cost `inv`, normalized.
   - `n >= 4`: every corridor lower bound is `≼ x^2 log x`. It is `≼ x^2` if
     `H_(n-1)` is undistorted in `H_n`, which is the open question of
     Burillo–Cleary–Martino–Röver.

So one-ray HNN corridors cannot prove `δ_(H_3) ≻ x^3`. For `n >= 4` they
cannot prove any bound beyond `x^2 log x`. Any proof of a larger lower bound
has to get area from the `t`-free regions of the diagram (cells of `R_0`),
not from corridor cells.

**Remark (no one-letter HNN over H_2 for m >= 4).** The quadratically
distorted subgroup `H_2 ≤ H_m` (BCMR Theorem 5.1) is not the base of any
one-stable-letter decomposition of `H_m` for `m >= 4`. The translation map
`H_m → Z^m` has image of rank `m - 1 >= 3`, but the image of `<H_2, g>` has
rank at most `2`.

Proof: `houghton-hnn-corridor-cap-proof`.
