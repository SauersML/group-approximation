---
rg: 2
id: abstract-twisted-bt-type-fn-criterion
kind: claim
title: For every action G on S, the abstract twisted Brin--Thompson group SV_G is finitely presented iff the action is of type [A_2], of type F_n iff it is of type [A_n], and of type FP_n iff it is of type [HA_n]
distinct_from:
  twisted-brin-thompson-type-fn-criterion: that is the faithful case (Belk--Zaremsky's conjecture); this removes faithfulness, answering the Fournier-Facio--Wu--Zaremsky conjecture for abstract twisted Brin--Thompson groups.
  abstract-btb-pairs-fp-and-relatively-simple: that imports FFWZ Theorem 4.1(ii) for type [A_2]; this re-proves the sufficiency half of that theorem by a route that avoids the gap recorded in ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel.
  twisted-brin-thompson-type-fn-implies-type-an: that is the necessity half for all n, proved by FFWZ through a quasi-retraction; this adds sufficiency for every action.
---

**ESTABLISHED** by `abstract-twisted-bt-type-fn-colored-stein-proof` (lane proof, 2026-09-18).
Referee a (proof gaps): **PASS**,
`research/artifacts/gq-referee-a-abstract-twisted-bt-type-fn-criterion.md` (efa4f3b5c), nits
applied. Referee c (independent second pass): **PASS**,
`research/artifacts/gq-referee-c-abstract-twisted-bt-type-fn-criterion.md` (72d2941ac).
Referee b (citations): **PASS** (68ed8a399). No priority claimed; bounded literature search
as on `twisted-brin-thompson-type-fn-criterion`.

## Statement

Let a group `G` act on a non-empty set `S`, faithfully or not, and let `SV_G` be the abstract
twisted Brin--Thompson group (FFWZ, arXiv:2603.24687v2, Definition 2.12). For `n ∈ N`:
1. `SV_G` is of type `FP_n` iff `G ↷ S` is of type `[HA_n]`;
2. `SV_G` is finitely presented iff `G ↷ S` is of type `[A_2]`;
3. `SV_G` is of type `F_n` iff `G ↷ S` is of type `[A_n]`, and of type `F_∞` iff it is of
   type `[A_∞]`.

Necessity in all items is FFWZ Corollary 4.18 (`twisted-brin-thompson-type-fn-implies-type-an`).
Its quasi-retraction (Proposition 4.17) is cited together with the realization of
`abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one`, which makes the germinal
twists in `G` well defined.
Sufficiency is new here:
- in item 1, for every `n ≥ 3`;
- in items 2 and 3, for non-faithful actions: FFWZ Theorem B(ii), (iii) had a proof with a
  gap, recorded in `ffwz-nonfaithful-stein-stabilizers-contain-canonical-kernel`.

**FFWZ's conjecture.** Item 3 is the conjecture FFWZ state in their §1.2 (text lines
115–117): "we conjecture that SV_G is of type F_n if and only if G ↷ S is of type [A_n]".

## Mechanism

1. Realize `SV_G` as the `S`-colored subgroup `Σ` of the faithful group `S'V_G`, where
   `S' = S ⊔ G` (`abstract-twisted-bt-group-is-colored-subgroup-of-faithful-one`).
2. `Σ` acts on the `S`-colored Stein complex of `S'V_G`. Its vertex stabilizers are the
   wreath products `G ≀ Σ_m`, not their preimages under a quotient.
3. The Belk--Zaremsky connectivity analysis is carried out inside a faithful groupoid of
   homeomorphisms and uses only `S`-colored forests. So it applies to this complex.
4. From there:
   - the interval filtration of `twisted-bt-type-fn-interval-filtration-proof` gives `FP_n`;
   - a `π_1` version of the same filtration, with Brown's presentation theorem, gives
     finite presentation.

## Consequences for the graph

- `abstract-btb-pairs-fp-and-relatively-simple`, item 1, and the nodes resting on it
  (`relatively-simple-removal-via-twisted-product-actor`,
  `relatively-simple-removal-between-pbh-and-bh-of-quotient`,
  `bh-product-closure-via-relatively-simple-kernel-removal`, and the others listed on the gap
  node) are supported again by this node in place of the FFWZ proof. Their owners should add
  it as a requirement.
- FFWZ Theorem C (Boone--Higman implies relative permutational Boone--Higman), in its "hence"
  form, is again fully proved: every finitely presented simple group sharply embeds in a
  finitely presented relatively simple abstract `SV_G`.

## Lesson for general BH

For twisted Brin--Thompson groups, finiteness is a property of the action alone and does not
depend on faithfulness: `SV_G`, faithful or abstract, has exactly the finiteness of
`Z ≀_S G`. So the kernel-removal problem (FFWZ Question 5.9) is purely about the action
images. It never concerns finite presentation of the ambient relatively simple group, which
is automatic from `[A_2]`.

## Referee (bh-ref-ffwz, 2026-09-18): PASS for item 2 (fourth independent pass)

This pass focuses on item 2, finite presentation from `[A_2]`, which is what FFWZ Q5.9 part 2
needs. I checked, by hand:
- `abstract-twisted-bt-colored-subgroup-proof`;
- Step 1 and Step 3 of `abstract-twisted-bt-type-fn-colored-stein-proof`;
- the statement of `stein-complex-elementary-intervals-are-grid-spheres`;
- the `[A_n]` definition, in the FFWZ arXiv TeX.

Results:
- **Realization.** Ψ is injective. If Ψ(h) = id, each leaf brick maps to itself, so each
  coordinate permutation `τ_{g_i}` is trivial. Then `g_i` fixes the free summand `G ⊆ S'`,
  so `g_i = 1`, and faithfulness of `SV` finishes. The `S`-colored subgroupoid is closed
  under composition, because `G` preserves the summand `S`.
- **Stabilizers.**
  - Vertex stabilizers are exactly `G ≀ Σ_r`, and Σ is transitive on each rank.
  - Short-edge stabilizers are **exactly** a conjugate of `Stab_G(s) × (G ≀ Σ_{r−1})`, not
    just commensurate with it. Twists at the split leaf must fix `s`, by
    `x_{g.s} g = (g⊕g) x_s` and the fact that distinct colors give distinct partitions.
  - Under `[A_2]` these stabilizers are finitely presented and finitely generated
    respectively.
- **The π_1 filtration is correct.**
  - Attaching `|I| = v * w * |(v,w)|` along `∂I = Σ|(v,w)|` is correct. `(v,w) ≠ ∅` for
    length ≥ 2, and the open cells of different intervals are disjoint.
  - Contractible boundaries and `S^{e−1}` with `e ≥ 3` do not change π_1.
  - The `e = 2` generators (the square, and the six-element hexagon of the grid-spheres
    example) are short-edge loops. Chains in one component stay in that component.
  - Attaching 2-cells along a superset of generators keeps `Y` simply connected.
- **Finiteness of orbits.** There are finitely many orbits of vertices, short edges and 2-cells:
  - ordered pairs `(s at i, t at j)`: orbits(S)²;
  - one-leaf 2-subsets: finite, from finitely many orbits on `S²`.
  Brown needs no 2-cell stabilizer condition, and the action is rigid.
- **Morse threshold.** For simple connectivity of `X^S_m`,
  `min(ν(r/2)−2, log_2(r/2)−2) ≥ 1` needs `r ≥ 22`.
- **Nit (countability).** BZ assume `S` countable. That holds automatically on the
  sufficiency side: `[A_1]` forces `G` finitely generated with finitely many orbits, so `S`
  and `S' = S ⊔ G` are countable. It is worth one sentence in the statement.
- **Not re-read at source.** Brown 1984 (the presentation theorem) and Hatcher–Wahl Prop 3.5
  (complete join complexes) were checked against their standard statements from memory,
  as earlier referees also did. Neither was re-read here.

With this PASS, `fp-relatively-simple-pair-with-unsolvable-simple-quotient`, and so the
second part of the FFWZ Q5.9 "no", no longer depends on FFWZ Theorem B's printed proof.
