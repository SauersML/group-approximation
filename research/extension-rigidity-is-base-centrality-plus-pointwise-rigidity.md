---
rg: 2
id: extension-rigidity-is-base-centrality-plus-pointwise-rigidity
kind: claim
title: An SFT extension is quantum rigid exactly when every quantum family has central base idempotents and the fibre over each base point is rigid relative to that point, on spaces of any dimension
distinct_from:
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that reduces rigidity of one transplant to its centrality statement (C) on finite-dimensional spaces; this proves the reduction for every extension over every group on spaces of any dimension, and shows that centrality is the only obstruction beyond pointwise rigidity.
  path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is: that pulls fibre families back along one fold (a necessity statement); item 2 here is the general necessity statement for every base point, and item 1 is the converse under centrality.
  deterministic-extensions-of-rigid-sfts-are-rigid: that proves rigidity of one class of extensions by propagation; in that proof centrality comes for free from determinism, so it is an instance of item 3.
  quantum-rigidity-is-product-stable: that is the case of a product group, where centrality again comes from propagation.
---

**ESTABLISHED** through `extension-rigidity-localization-proof` (lane bh-free-09, 2026-09-18;
elementary lane proof, one adversarial referee PASS (see Referee); no priority claimed).

## Setting

Quantum families (Q1)–(Q3) and `D`-quantum rigidity are as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity`. There is no restriction on the field,
and none on the dimension of the space `W_0`.

- `Λ` is finitely generated, `B` and `F` are finite alphabets, and `Y ⊆ B^Λ` and `X ⊆ (B × F)^Λ`
  are SFTs whose forbidden patterns lie in balls of radius `≤ D`. The `B`-projection of `X` lies
  in `Y`. This covers every layered SFT with one designated *base* layer: skeletons, germ fields,
  flow layers.
- For a `D`-family `E_(b,f)(u)` of `X`, the *base marginals* are `E^B_b(u) = Σ_f E_(b,f)(u)` and
  the *fibre marginals* are `E^F_f(u) = Σ_b E_(b,f)(u)`.
- The family is **base-central** if every `E^B_b(v)` commutes with every `E_(b',f)(u)`, for all
  sites `u, v`, near or far. **(C_D)** is the statement that every `D`-family of `X` over `k` is
  base-central.
- Let `y ∈ Y`. A **`y`-relative `D`-family** on a space `W` is a family of idempotents `G_f(u)`
  (`f ∈ F`, `u ∈ Λ`) satisfying (Q1) and (Q2) for the fibre letters, and
  - (Q3_y): for every `p ∈ Λ` and every `φ ∈ F^(pB_D)` such that no point of `X` has base
    letters `y|_(pB_D)` and fibre letters `φ` on `pB_D`, the product `∏_(w ∈ pB_D) G_(φ(w))(w)` is
    `0`.

  `X` is **`D`-rigid relative to `Y` at `y`** if every `y`-relative `D`-family commutes. This is a
  question about the single fibre `X_y = {f : (y, f) ∈ X}`, with the base frozen at the classical
  point `y`. It is not shift-invariant: `λ·X_y = X_(λ·y)`.

## Theorem

1. **Localization.** Let `E` be a base-central `D`-family of `X` on `W_0`. For each `y ∈ Y` there
   is a quotient space `W_0 → M_y` on which every fibre marginal acts. The induced operators form a
   `y`-relative `D`-family, and every base marginal `E^B_b(u)` acts on `M_y` as the scalar
   `[y(u) = b]`. `E` commutes if and only if its localizations at all `y ∈ Y` commute.
2. **Lifting.** If `G` is a `y`-relative `D`-family on `W`, then `E_(b,f)(u) = [y(u) = b] G_f(u)` is a
   base-central `D`-family of `X` on `W`, and it commutes if and only if `G` does.
3. **Decomposition.** `X` is `D`-quantum rigid over `k` if and only if
   - (C_D) holds, and
   - `X` is `D`-rigid relative to `Y` at every point `y ∈ Y`, over `k`.

No hypothesis on `Y`, `Λ`, freeness, minimality or amenability is used. Rigidity of `Y` enters
only as the part of (C_D) that says base marginals commute with each other. So when `Y` is
rigid, (C_D) reduces to the statement that base marginals commute with fibre marginals.

## Consequences

- **Busemann transplants, any dimension.** Take the germ layer `X_Ω^K` as base and the tile
  layer as fibre in `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid`. Its step 2 argument
  (quantum R3, operator coherence, then rigidity of the corner-deterministic `Y`) uses only that the
  germ marginals act as `0/1` scalars given by a legal germ field. That is exactly the situation on
  each `M_y`, where the germ field is a genuine point `y = x_c` of `X_Ω^K` (the coding image of the compact
  space `Ω`). (H_Ω) is used only to make the germ layer a finite-type base. Granting that
  sketch, under that node's hypotheses **`Y_Δ` is quantum rigid if and only if (C) holds, on spaces
  of every dimension**. This removes the finite-dimensional restriction ("not written out") from the
  partial result.
- **The ABHT shift on `F_n × Z`.** Take the flow layer `Y_f` (rigid) as base. By item 3, the shift is
  rigid if and only if (C) holds and it is rigid relative to each flow point. By
  `path-folded-sfts-are-quantum-rigid-only-if-the-fibre-is`, rigidity of the `Z²` fibre is
  necessary for the latter. That the relative problem at a flow point is *equivalent* to rigidity of
  the `Z²` fibre (coherence of tiles along the fibres of the Busemann fold) is expected, not checked.
- **Where (C) is already known.** In deterministic extensions (Step 5 of
  `deterministic-extension-rigidity-proof`) and in products over product groups
  (`quantum-rigidity-is-product-stable`), (C) holds because fibre operators are propagated from
  base operators. In the aligned plane-constant simulations of
  `copy-constraints-make-simulation-skeleton-and-data-commute`, skeleton and data commute with each
  other, but centrality against far computation-layer idempotents is not shown.

## Lesson for general BH

- **All of G2 in a layered design is centrality.** For any master-route SFT built in layers (a base
  such as a skeleton, germ field or flow, with data or tiles on top), quantum rigidity is exactly
  two things:
  - (C): base idempotents are central in every quantum family;
  - pointwise problems in which the base is one frozen classical point.
- **The pointwise problems are where the one-layer tools work.** Determinism, coherence and folds
  handle them in every known case.
- **So new G2 mechanisms must target (C).** The known sources of (C) are determinism of the fibre
  and product structure of the group. Transplants, the ABHT fold and simulations have neither, which
  is exactly why they are open.
- **Rigidity of the base does not help.** It only makes base marginals commute with each other.
  Every family obtained by conjugating or differentiating base families by fibre operators commutes
  automatically, so such families carry no information about (C).

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS

I checked `extension-rigidity-localization-proof` line by line.

- **Step 1.** Base-centrality reduces commutation to the fibre marginals, and
  `E^B_b E^F_f = E_(b,f)` holds at a single site.
- **Step 2.** `ψ` is a unital homomorphism, because the base partitions of unity commute pairwise.
- **Step 3.**
  - `N_z` is a directed union, so it is a subspace.
  - It is invariant under the commutant of `R`, and the scalar action `[z(u) = b]` on `M_z` is
    correct.
  - The compactness lemma is correct: `w ∈ ψ(1_(U_z))W_0` gives `ψ(1_(V_z))w = 0`. Then take a
    finite clopen partition subordinate to the cover.
- **Step 4.** A point `z ∉ Y` contains a forbidden ball pattern `β`. Then `ψ(1_[β]) = 0` by (Q3),
  so `M_z = 0`.
- **Step 5.** In (Q3_y), the `β = y|` term is killed by (Q3), and the terms with `β ≠ y|` land in
  `N_y`.
- **Step 6.** The commutator lies in the commutant of `R`, so the compactness lemma applies.
- **Steps 7–8.** The lift is a genuine `D`-family, and the equivalence is exact.

The theorem holds as stated, over any field and in any dimension.

**Not checked:**
- the "Consequences" bullets, which rest on the unrefereed step-2 sketch of
  `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid`;
- the last lesson bullet, that conjugated or differentiated base families "commute automatically".
