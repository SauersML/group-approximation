---
rg: 2
id: blind-commutants-of-push-families-in-ct-p-z-are-trivial
kind: claim
title: In Kohl's CT_P(Z), a piecewise-canonical map that commutes with a binary push family and preserves that family's germ data is the identity; so in any copy of Brin's 2V the pushes of each stack must read hidden fibre data that the other stack's group moves
requires:
  - brin-thompson-nv-needs-n-minus-one-primes-in-ct-z
  - ct-p-z-is-not-a-product-shift-full-group
distinct_from:
  ct-p-z-is-not-a-product-shift-full-group: that proves the commutant lemma for single canonical pushes (item 3); this removes the single-piece hypothesis, needing only that the commuting map preserves the pushes' germ data.
  brin-thompson-nv-needs-n-minus-one-primes-in-ct-z: that bounds the dimension and reduces a copy of 2V in CT_{3}(Z) to commuting Cuntz families; this constrains those families (and the symmetric-power case) from inside.
---

**ESTABLISHED** for items 1–3 (lane proof, elementary; not independently reviewed; no priority
claimed). **OPEN:** does `2V` embed in `CT(Z)`? This node rules out every "blind" design but does not
decide the question. Kourovka 17.58 stays OPEN.

## Setting

- `Z ⊆ Ẑ_P` is clopen, and `μ` is Haar measure.
- A piecewise-canonical map acts on each piece of a finite box partition by `y ↦ cy + d`, with
  `(c,d) ∈ Aff(Q)`; call this the *germ datum*.
- For maps `s_0, s_1` write `s_u = s_{u_1} ∘ … ∘ s_{u_n}`, and `S_u(w) ∈ Aff(Q)` for the germ datum
  of `s_u` at `w`.

## Statement

1. **Blind commutant lemma.**
   - Hypotheses:
     - `s_0, s_1 : Z → Z` are piecewise-canonical injections with disjoint ranges.
     - `π : Z → Y` is any map such that (i) the germ datum of `s_r` at `z` depends only on `π(z)`,
       and (ii) `π(s_r z)` depends only on `(r, π(z))`.
     - `c : Z → Z` is piecewise canonical, `c ∘ s_r = s_r ∘ c` for `r = 0, 1`, and `π ∘ c = π`.
   - Conclusion: `c = id`.
2. **Label form.** Take `π(z)` to be the tree of germ labels `u ↦` (germ data of `s_0, s_1` at
   `s_u z`). Then: every piecewise-canonical `c` that commutes with `s_0, s_1` and maps each piece of
   their germ partition `𝒫` into itself is the identity.
3. **Consequences for 2V.** Let `ρ : 2V → CT_P(Z)` be an embedding, extended by Matte Bon to
   `ρ̃ : G̃^{[r]}_{2V} → G̃_P|Z` (any `r`, any finite `P`). Let `s_i = ρ̃(S^{(1)}_i)` be the images
   of the first stack's pushes, and `𝒫` their germ partition.
   - (a) No nontrivial element of `ρ(1 × V)` maps every piece of `𝒫` into itself.
   - (b) For `r = 1` (forced when `P = {3}`), with `q : Z → C × C`, there is no cylinder `C_w`
     over which `𝒫` is `q`-saturated. On every `q^{-1}(C × C_w)`, the first stack's pushes depend
     on data inside the `q`-fibres.
   - The same holds with the stacks exchanged.
   - In the product model, where `2V` acts on itself, the pushes are blind. So no copy of `2V` in
     `CT(Z)` looks like `2V`: each stack's push must read a hidden coordinate that the other stack's
     group moves.

## Proof

**Item 1.**
- **Conjugation formula.** From `c s_u = s_u c`, taking germs at `w` gives
  `[c]_{s_u w} = [s_u]_{cw} [c]_w [s_u]_w^{-1}`. Along the paths from `w` and from `c w`, (ii) and
  `π(cw) = π(w)` give equal `π`-values, and then (i) gives equal germ data: `S_u(cw) = S_u(w)`. Writing
  `C(y)` for the germ datum of `c` at `y`, this means `C(s_u w) = S_u(w) C(w) S_u(w)^{-1}` in
  `Aff(Q)`.
- **Counting words.** Fix `n`.
  - The slopes of `S_u(w)`, `|u| = n`, are products of `n` slopes from a finite set of `P'`-smooth
    ratios. They take at most polynomially many values in `n`, so some slope class contains at least
    `2^n / poly(n)` words.
  - The points `s_u(w)` are distinct, since ranges are disjoint. So within a slope class `C`, the
    translations `D_u` of `S_u(w) = (C, D_u)` are distinct.
- **Slope `≠ 1`.** Suppose `C(w)` has slope `≠ 1`, with fixed point `y_w ∈ Q`. Then `C(s_u w)` has
  fixed point `S_u(w)(y_w) = C y_w + D_u`. These points are distinct within a slope class, so they
  are unbounded in number. But `c` has finitely many pieces, hence finitely many fixed points of germ
  data. Contradiction. So every germ of `c` is a translation, `C(w) = (1, d_w)`.
- **Slope `1`.** Then `C(s_u w) = (1, C_u(w) d_w)`, where `C_u(w)` is the slope of `S_u(w)`.
  - If `d_w ≠ 0`, finiteness forces `sup_u C_u(w) < ∞`.
  - That happens only on a null set. If `W_K = {w : C_u(w) ≤ K for all u}` had positive measure, the
    disjoint sets `s_u(W_K)`, `|u| = n`, would each have measure at least `μ(W_K)/K`, and their total
    `2^n μ(W_K)/K` would exceed `μ(Z)`.
  - So `d_w = 0` almost everywhere. Every piece of `c` has positive measure, so `c = id`.

**Item 2.** This `π` satisfies (i) and (ii) by construction. Since `c` commutes with the `s_r`,
`π(cz) = π(z)` is equivalent to `c` preserving the labels at every `s_u z`, i.e. at every point of
`Z`. That is: `c` maps each piece of `𝒫` into itself.

**Item 3.**
- **(a).** `ρ(1 × h)` commutes with the `s_i`, because `1 × h` commutes with `S^{(1)}_i` in the
  pseudogroup and `ρ̃` is a morphism. The `s_i` are injective on `Z` with disjoint ranges, for every
  `r`. Item 2 then gives `ρ(1 × h) = id`, so `h = id` since `ρ` is injective.
- **(b).** Suppose `𝒫 ∩ q^{-1}(C × C_w) = {q^{-1}(Q_P)}` with the `Q_P` clopen in `C × C_w`.
  - Refine to a depth `L` at which every `Q_P` is a union of product cylinders. Take `w′ ⊇ w` with
    `|w′| ≥ L`, and `h ≠ 1` supported in `C_{w′}`.
  - Then `1 × h` preserves every `C_{a′} × C_{w′}`, hence every `Q_P`. Also `ρ(1 × h)` is the
    identity off `q^{-1}(C × C_{w′})`, by locality.
  - So `ρ(1 × h)` preserves every piece of `𝒫`, which contradicts (a). `∎`

## Why the diagonal matters

In `2V` itself, the commutant of the first stack's pushes is `1 × V`, and item 1 fails. A germ of
`1 × h` fixes a whole line, so conjugating it produces no new fixed points. In `CT_P(Z)` every germ
datum is one affine map of `Q` acting on all coordinates at once, so each nontrivial non-translation
germ has a single fixed point. Conjugation by a binary family then produces exponentially many fixed
points from finitely many pieces. That count is where "arithmetic ≠ product" becomes a proof.

## What remains

A copy of `2V` in `CT_P(Z)` would need a hidden fibre coordinate with three properties:
- each stack's pushes read it;
- the other stack's `V` moves it;
- all of this happens with finitely many affine pieces.

No such design is known, and none is excluded. The sharpest next test: take `P = {3}` and the
3-adic odometer fibres of `conway-amusical-permutation-is-the-full-three-shift`, item 6, as the
candidate hidden coordinate.

**Lesson for general BH.**
- **Commuting is expensive in arithmetic hosts.** A map commuting with a self-similar push family is
  the identity unless the pushes read what it moves. This is a conjugation-count argument that works
  in any host whose germs are single affine maps: finitely many pieces cannot absorb exponentially
  many conjugate fixed points.
- **Constructions that need commuting independent structures** (writers, product hosts, `Z^2`-grids
  of stacks) must therefore supply hidden, mutually-read coordinates in such hosts. That coupling is
  what distinguishes `CT_P(Z)` from `nV`, and it is where any proof that `2V ⊄ CT(Z)` must go.
