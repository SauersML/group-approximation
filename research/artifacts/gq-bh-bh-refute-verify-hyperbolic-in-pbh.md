# Adversarial check: `hyperbolic-groups-lie-in-the-permutational-class` and its product consequences (bh-refute, 2026-09-18)

Rotation item 1 (fa1747017). Verdict: **PASS**. This is an independent adversarial check, on top of the
two existing referee PASSes (2bdad9399, 9ec4a1a7c). It extends to the unreviewed closure chain behind item 3.

## Items 1–2 (full contracting RSGs are type (A) actors)

- **Type (A) definition.** It is checked against Zaremsky's form (faithful, f.p., f.g. point stabilizers,
  finitely many orbits of 2-subsets; `type-a-action-gives-boone-higman-for-subgroups`). The four BBMZ inputs
  (Thm 3.1 f.p., Prop 5.4 high transitivity, Prop 5.8 f.g. finite-set stabilizers, faithfulness on a dense
  orbit) give exactly these. `|S| >= 2` holds because the orbit is dense in a Cantor set, so high
  transitivity gives one orbit of 2-subsets.
- **Stabilizers at every point of the orbit.** These are conjugate, so this is fine.
- **Contracting self-similar groups.** A contracting group is finite-state (all sections at depth
  `>= n(g)` lie in the finite nucleus). So it sits in the full contracting RSG, as in BBMZ Cor. 5.2. This is correct.
- **Attack: need the full RSG to be finitely generated?** No. Theorem 3.1 gives finite presentation of the full
  contracting RSG itself.

## Item 3 (products): the closure chain, re-derived

The direct-product, finite-index, free-product and graph-product closures are all reviewed or refereed on
main. The **restricted-wreath** bullet rests on three nodes marked "not independently reviewed". I checked
all three:

1. `pbh-free-action-via-relative-automorphisms-proof`.
   - `G ≤ E` with `E` a type (A) actor.
   - `E` is f.p. with solvable WP (Zaremsky Cor. B).
   - `E ≤ M`, a f.p. simple MIF group, by BFFHZ Thm C (i)⇒(iv). The hypothesis "finitely generated" is met by
     `E`.
   - `τ_g : x_1 ↦ x_1 g` gives a homomorphism `M → Aut_M(M * F_2)`, and it is injective.
   - On `S ≅ M × M`, `τ_g` acts by `(m_1, m_2) ↦ (m_1 g^{-1}, m_2)`, which is free. There are `|M| = ∞`
     orbits (MIF ⇒ infinite).
   - Countable free `G`-sets therefore inject equivariantly.
   - **Correct.**
2. `type-a-lamp-wreath-with-type-a-lamps-proof`.
   - (LW) is an action.
   - It is faithful.
   - It is f.p. by Cornulier: `Λ ≠ 1` and `Γ` f.p., f.g. stabilizers, finitely many orbits on `S²`.
   - Stabilizer generation: `Stab_Γ(s)` has finitely many orbits on `S∖{s}`, since these correspond to
     orbits of ordered pairs.
   - Finitely many orbits on ordered pairs of `S × Y`, in both cases `s ≠ s'` and `s = s'`.
   - All re-derived. **Correct.**
3. `pbh-wreath-closure-via-free-relative-automorphism-orbits`.
   - Pulling back along the finite-fibred `π : G × I → X` is injective and equivariant.
   - Supports stay finite, and **this is exactly where finite stabilizers are used**.
   - Pushing forward along `ι` into `Λ^(S)` is equivariant on and off `ι(X~)`.
   - The composite lands in the type (A) group `Λ wr_S Γ`.
   - **Correct.**

The mixed examples cite ESTABLISHED nodes:
- `aut-free-groups-satisfy-permutational-boone-higman`, a literature import;
- `char-zero-linear-groups-satisfy-permutational-boone-higman`;
- `e-type-artin-groups-satisfy-permutational-boone-higman`, which has an independent review.

## Named-problem bearing

These are the partial answers on BBMZ 5.3(10) and 5.3(11), for products of hyperbolic groups.
- Direct products of automatic groups are automatic (ECHLPT; standard).
- Graph products of automatic groups are automatic (Hermiller–Meier 1995).

These are correctly flagged as unpinned and are not used in items 1–3. **No overclaim.**

## Attacks tried (all failed)

- Ordered pairs vs 2-subsets mismatch between BFFHZ and Zaremsky: equivalent on sets with at least 2
  points, as the lamp node notes.
- Countability of `S` in the free-orbit step: `S = M × M` is countable.
- Hidden f.g. hypothesis on `G` in Theorem C: it is applied to `E`, which is f.p.
