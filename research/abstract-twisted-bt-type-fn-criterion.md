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
applied. Second pass (gq-referee-c) and citation pass (gq-referee-b) requested. No priority claimed.

## Statement

Let a group `G` act on a non-empty set `S`, faithfully or not, and let `SV_G` be the abstract
twisted Brin--Thompson group (FFWZ, arXiv:2603.24687v2, Definition 2.12). For `n ∈ N`:
1. `SV_G` is of type `FP_n` iff `G ↷ S` is of type `[HA_n]`;
2. `SV_G` is finitely presented iff `G ↷ S` is of type `[A_2]`;
3. `SV_G` is of type `F_n` iff `G ↷ S` is of type `[A_n]`, and of type `F_∞` iff it is of
   type `[A_∞]`.

Necessity in all items is FFWZ Corollary 4.18 (`twisted-brin-thompson-type-fn-implies-type-an`).
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
