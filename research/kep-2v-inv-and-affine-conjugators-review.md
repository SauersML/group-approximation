---
rg: 2
id: kep-2v-inv-and-affine-conjugators-review
kind: claim
title: Referee review of e486fed877 (bh-glnq-fresh) — item 8, (Inv) automatic for every degree-preserving H, matches Li's ex:ZS at source; item 9, a tree automorphism conjugating a unit translation to another is affine, is correct; item 10, root-gluing amalgams of Möbius pieces lie in PGL_2(Q_2) and so see finitely many primes, is correct for its stated class
distinct_from:
  kep-2v-hosts-hausdorff-perfect-review: that reviewed be9b68158e and first observed (Inv) automatic; this checks the node's own item 8 and the new items 9–10.
  kep-2v-hosts-carry-q-x-2-iff-h-has-odometer-roots: the lane node under review.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19).** No priority claimed.

- **Item 8 ((Inv) automatic): PASS at source.** Li, arXiv:2110.04505v2, l.2332 defines (Inv) as three
  conditions: `𝔊.𝔖 ⊆ 𝔖𝔆^*`, `X(g.𝔳; g.𝔢) ∈ 𝔛`, and `g.γ ∈ Γ𝐂^*`. Example `ex:ZS` (l.2372) states all
  three for self-similar actions with `𝔡(g.a) = 𝔡(a)` in the degree setting, with `𝔛` and `Γ` built as in
  §`s:Gars-deg`. `H` acts on colour-1 edges preserving length and fixes colour-2 edges, so this holds
  for every such `H`, including the rational Iwahori group.
- **Conditional corollary: PASS.** It combines items 5–8 with Matui's `simple2`, reviewed in
  `kep-2v-hosts-hausdorff-perfect-review`. The only hypotheses left are these: `H` is self-similar,
  contains `τ` and the `Z_(2)` translations, is locally faithful, and is finitely presented.
- **Item 9 (conjugators between unit translations are affine): PASS.**
  - `στ_a = τ_bσ` gives `σ(x + na) = σ(x) + nb`.
  - `Za` is dense because `a` is a unit, and `σ` is continuous (an isometry). So
    `σ(y) = σ(0) + (b/a)y`.
  - **Two additions.** First, `b` is then a unit and `b/a ∈ Z_2^×`, since `σ` is an isometry and `τ_b` is
    minimal like `τ_a`. Second, `σ(0) ∈ Z_2` is arbitrary, so the conjugator lies in `PGL_2(Q_2)`, and
    in general not in `PGL_2(Q)`. The node says `Q_2`, which is correct.
- **Item 10 (prime-moving amalgams collapse): PASS for the stated class.**
  - Suppose every piece consists of Möbius maps over `Q_2` and every gluing element conjugates a unit
    translation to another inside `Aut(T_2)`. Then the generated group is a finitely generated subgroup
    of `PGL_2(Q_2)`. By `fg-linear-groups-have-roots-at-finitely-many-primes`, which is stated over any
    field, `τ` has roots in it at only finitely many primes.
  - The inference to "the roots must come from non-conjugation words" is correct only for constructions
    of this shape. Amalgamations identifying non-translation subgroups, or pieces that are not Möbius,
    are outside it. The node's wording ("glued along elements that carry roots …") already fixes this
    class, so no repair is needed, only care in later citations.
