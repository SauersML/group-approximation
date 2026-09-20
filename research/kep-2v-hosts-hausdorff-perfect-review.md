---
rg: 2
id: kep-2v-hosts-hausdorff-perfect-review
kind: claim
title: Referee review of be9b68158e (bh-glnq-fresh) — local faithfulness is exactly Exel–Pardo pseudo-freeness for a faithful self-similar H, which gives Hausdorffness (checked at source); (F), right cancellation and perfectness of 2V_H PASS; and (Inv), flagged unchecked, is in fact automatic by the same Li Example ex:ZS paragraph, so the conditional corollary needs only that H be finitely presented, locally faithful and contain the Z_(2) translations
distinct_from:
  kep-2v-hosts-odometer-roots-review: that reviewed 12ec78a007 and located the conditions in Li and Matui; this checks the addendum be9b68158e that verifies them.
  kep-2v-hosts-carry-q-x-2-iff-h-has-odometer-roots: the lane node under review.
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19).** No priority claimed. Sources were read as arXiv LaTeX
e-prints on MSI (`/projects/standard/hsiehph/sauer354/refs/`):
- Exel–Pardo, arXiv:1409.1107, section "The Hausdorff property", Def. `EssFree`;
- Li, arXiv:2110.04505v2, l.1454 (F), l.2332 (Inv), l.2372 (`ex:ZS`);
- Matui, arXiv:1210.5800v3, the subsection "Purely infinite groupoids" and Thm `simple2`.

## Hausdorff: PASS, and it matches Exel–Pardo

**The direct argument is correct.**
- Suppose two germs cannot be separated. Then `h` has a nontrivial germ at `z`, and `z` lies in the
  closure of the interior of `Fix(h)`.
- On the piece `R ∋ z` of `h`'s partition, `h = (p, η, w)`. Agreement on a subcone forces `w′ = w`. It
  also forces `p′η(q) = pq` as words, because tree automorphisms preserve cone level. So `p′ = p` and
  `η` is the identity on `C(q)`.
- By local faithfulness `η = 1`, so `h = id` on `R`, which is a contradiction.

**At source.**
- Exel–Pardo, Def. `EssFree`: `(G, E, φ)` is "pseudo free if, whenever `(g, e) ∈ G × E^1` is such that
  `g e = e` and `φ(g, e) = 1`, then `g = 1`". This is equivalent to no nontrivial element strongly
  fixing a path.
- Their section "The Hausdorff property", Proposition: "If `(G, E, φ)` is pseudo free, then
  `𝒢_(G,E)` is a Hausdorff groupoid". The proof goes through E*-unitarity.
- Their Theorem `MainHausdorff`: Hausdorff "⟺ for every `g` in `G`, there are at most finitely many
  minimal strongly fixed paths for `g`".

**Local faithfulness is exactly pseudo-freeness.**
- For a **faithful** `H ≤ Aut(T_2)`, `η` strongly fixes `q` iff `η` is the identity on `C(q)`. So local
  faithfulness is pseudo-freeness.
- On the 2-graph, colour-2 edges are fixed and carry the restriction `η`, so strongly fixed mixed paths
  reduce to colour-1 prefixes.
- Local faithfulness is sufficient but not necessary: by `MainHausdorff`, finitely many minimal strongly
  fixed paths per element already suffice.
- Exel–Pardo treat 1-graphs. The node's direct germ argument covers the 2-graph case itself.

**Effectiveness.** The node's argument is tautological at the level of germs of `2V_H`. What is needed is
that Li's groupoid, the germ groupoid of `I_l(𝔇)`, is effective. That holds for any faithful self-similar
`H`: an element `(μ, η, μ)` that is the identity on `μνX` strongly fixes `ν`, and so equals an idempotent
there. The conclusion stands.

## (F), right cancellation, (Inv)

- **(F): PASS.** Li l.1454: "(F) holds if for all `𝔳 ∈ 𝔆^0`, `a, b ∈ 𝔆^*(𝔳, 𝔳)` and
  `U = X(𝔳; 𝔢) ∈ 𝔛`, `[a, U] = [b, U]` in `𝐂` implies `a = b`." A nonempty constructible `U` contains a
  rectangle, so agreement there together with local faithfulness gives `η_1 = η_2`.
- **Right cancellation: PASS.** The quote at l.2372 is verbatim.
- **(Inv): automatic, not an open condition.**
  - Li l.2332 defines (Inv) as three statements:
    - `𝔊.𝔖 ⊆ 𝔖𝔆^*`;
    - `X(g.𝔳; g.𝔢) ∈ 𝔛`;
    - `g.γ ∈ Γ𝐂^*`.
  - The same `ex:ZS` paragraph (l.2372) states all three for degree-preserving actions over a right
    cancellative `P`, with `𝔛` and `Γ` built as in §`s:Gars-deg`: "…and for the Garside family `𝔖` …
    we have `𝔊.𝔖 ⊆ 𝔖𝔆^*`. Moreover … `X(g.𝔳; g.𝔢) ∈ 𝔛`, and … `g.γ ≔ (g.a_i) ∈ Γ𝐂^*`". Its conclusion
    then needs only the assumptions of `thm:deg` on `𝔆` and condition (F).
  - The assumptions of `thm:deg` on `𝔆` were verified for the product 2-graph in the `H = ⟨τ⟩` case.
    They concern `𝔆` alone and do not depend on `H`.
  - **Repair:** delete "(Inv) is the one condition not checked here" and cite l.2372.

## Perfectness: PASS

- `2V_H = ⟨2V, η_R⟩` via the factorization `g = v ∘ ∏(η_i)_(R_i)`.
- The `η_R` over proper rectangles are all conjugate by `2V` prefix maps, which commute with tail actions.
- Splitting `R` along the **second** coordinate gives `θ(η) = 2θ(η)`, so `θ(η) = 0`. Splitting along the
  first coordinate would not work, and the node correctly avoids it.
- `η_X` is the product of two proper-rectangle elements.
- `2V` is simple and nonabelian, so `2V ≤ D(2V_H)`.
- Matui's standing hypothesis for `simple2` is "an essentially principal étale groupoid whose unit space
  is a Cantor set", i.e. effective. Minimality and pure infiniteness come from `2V`.
- So `2V_H` is simple under local faithfulness.
- `[u, a] = a` follows from `uau^(-1) = a^2`.

## The example and the obstruction

- The rational Iwahori group is locally faithful, since Möbius maps are analytic. It contains
  `x ↦ x + c` for `c ∈ Z_(2)`, with `[[1,c],[0,1]] ∈ I_2 ∩ PGL_2(Q)`. It is not finitely generated. This is
  consistent with the node's statement that the remaining obstruction is finite generation or
  presentation of a non-linear `H`.

## Net

**Corrected conditional corollary.** If `H ≤ Aut(T_2)` is self-similar, contains `τ` and the `Z_(2)`
translations, is locally faithful, and is finitely presented, then `2V_H` is a finitely presented simple
group containing `Q ⋊ ⟨2⟩`. No Li condition remains open. The whole question is the existence of such an
`H`.
