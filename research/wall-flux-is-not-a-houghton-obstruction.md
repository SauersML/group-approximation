---
rg: 2
id: wall-flux-is-not-a-houghton-obstruction
kind: claim
title: The integer wall flux of a bounded full contracting RSG lives only on transfer germs; germ stabilizers see no flux, so every cell stabilizer of the germ complex is commensurable with an F_infinity group; Brown's Houghton obstruction needs flux at fixed ends over a locally finite base with boundedly many ends, and none of these holds, so the flux is absorbed by the zero-sum-completable germ complex, whose sublevels are cocompact, leaving one combinatorial lemma
requires:
  - torsion-defect-costs-nothing-in-bhm-germ-complexes
distinct_from:
  torsion-defect-costs-nothing-in-bhm-germ-complexes: that handles torsion defects and records the pentagon's infinite-order flux as open; this analyses whether that flux can obstruct F_n, finds no Houghton-type obstruction, and reduces F_infinity to a connectivity lemma for bounded-sum joins.
---

**Status.**
- **ESTABLISHED (lane proof, bh-finf-hyp, 2026-09-19; not reviewed):** items 1–4.
- **OPEN:** Lemma 5, with item 5a proved in boundary cases.
- No computation was run.

## Setting

- This is `torsion-defect-costs-nothing-in-bhm-germ-complexes`, with defect group `⟨Δ⟩ ⊆ H_0(G_Σ)` possibly
  infinite. For the right-angled pentagon RSG it is `⟨x⟩ ≅ Z`, and each reflection has fluxes
  `+x, +x, −x, −x` (`gq-bh-finf-hyp-pentagon-defect-class.md`).
- **The per-point bound.** `(L)_p/(B)_p` is finite, so each singular point carries finitely many B-germ classes.
  Since there are finitely many B-orbits of singular points, `|d| ≤ δ_max` for all singular germs.

## 1. The flux lives only on transfer germs; germ stabilizers see none

- For `p` fixed by `g` and `h`, the cocycle rule gives `d_{gh}(p) = d_g(p) + d_h(p)`. So
  `ψ_p : Stab_L(p) → ⟨Δ⟩`, `g ↦ d_g(p)`, is a character of the germ group `(L)_p`.
- `ψ_p` vanishes on `(B)_p` (canonical germs), and `(B)_p` has finite index in `(L)_p`. So `ψ_p` factors through a
  finite group, and **`ψ_p = 0` whenever `⟨Δ⟩` is torsion-free** (for example `Z` for the pentagon).
- Hence the pentagon's `±x` fluxes sit on **transfer germs**, i.e. germs at points the element moves. The
  reflection exchanges its paired singular points, which is consistent with this.
- **Global characters.** For a B-orbit `O` of singular points, `φ_O(g) = Σ_{p∈O} d_g(p)` is a homomorphism on the
  finite-index subgroup preserving each of the finitely many singular orbits.
  - It is nonzero exactly when some element's flux does not cancel inside one tail class.
  - It vanishes on commutators, so it is invisible in the simple envelope.
  - For the pentagon, whether a reflection's `+x` and `−x` points share a tail class was not computed.

## 2. How many fluxes a stabilizer sees: none

- Cell stabilizers of the germ complex are commensurable with `SingFix_L(M, M')`, whose elements fix `M'`
  pointwise. By item 1 their germs at `M` carry no flux (torsion-free case).
- **So `k = 0`**, bounded for every cell.
- `SingFix_L(M,M')` contains `Fix_B(M')` with finite index, since `(L)_M/(B)_M` is finite. `Fix_B(M')` is `F_∞`:
  an iterated ascending HNN extension of `V_(Σ,U)`, which is `F_∞` by Matui.
- **Contrast with Houghton `H_n`.** There the flux *is* a germ character at fixed points: translation lengths at
  the `n` ends, with germ quotient `Z`, over a locally finite base.

## 3. Why Brown's Houghton argument does not transfer

- **Houghton `H_n`.** It is `F_(n−1)` but not `F_n` (Brown) because of two features:
  - its non-flux part is `FSym`, locally finite and not finitely generated;
  - it has exactly `n` rays, so the join in each descending link has at most `n` factors and connectivity
    `≤ n − 2`.
- **Here both fail.**
  - The non-flux part `B = V_(Σ,E)` is `F_∞`.
  - The singular points form infinitely many points in finitely many dense B-orbits. So the descending link of a
    vertex with `h` hidden points is a join of `h` factors, with `h` unbounded.
- **The right count.** What matters for the Houghton mechanism is flux at fixed points (here none, `k = 0`) and
  the number of ends available to one descending link (bounded for Houghton, unbounded here). So **no Houghton-type obstruction arises**, at any `n`. This is consistent with BBMZ's finite
  presentation.

## 4. The zero-sum-completable germ complex is cocompact

- **Definition.** Let `K_0 ⊆ K = ∏'_p T_p` be spanned by the partial portraits that complete to total defect 0.
  With `h` hidden points and revealed total `c`, completable means `c ∈ −(D_{p_1} + ⋯ + D_{p_h})`. In particular
  `|c| ≤ h·δ_max`.
- `L` preserves `K_0`, since total defect is invariant, as in the parent node.
- **Finitely many orbits.** With `h ≤ n`, `|c| ≤ nδ_max` takes finitely many values. The parent node's count gives
  finitely many orbits of cells in each `K_{0,≤n}`. Cell stabilizers are commensurable with the groups of item 2, which are `F_∞`.

## 5. What remains: the bounded-sum join lemma

**Lemma 5 (open).** Take a vertex of `K_0` with `h` hidden points and revealed total `c`. Its descending link is
the complex of partial revealings `S ⊆ M` (with germs) that stay completable. It should be
`(h − 3 − C)`-connected, with `C` depending only on `δ_max`. In addition `K_0` should be contractible.

**5a (proved).** Take `δ_max = 1` and `c = h − 1`, a near-extreme boundary case.
- The link is the join of the defect-`(−1)` germ sets, with simplices allowed at most one defect-0 vertex.
- It is obtained from the full join of the `N_p`, which is `(h−2)`-connected, by attaching cones on joins over
  `h−1` points, which are `(h−3)`-connected.
- So it is `(h−2)`-connected.
- The extreme case `c = h` is a full join, also `(h−2)`-connected. The case `c = 0` removes only the top
  simplices of a full join, so it is `(h−3)`-connected.

**Consequence.** Lemma 5 together with items 2–4 and Bestvina–Brady gives `F_∞` for every bounded full contracting
RSG with a bounded defect group, torsion or not. The pentagon RSG and its twisted Brin–Thompson envelope would be
among them. Without Lemma 5 nothing is concluded, but **no Houghton-type negative answer to Question 1.2 comes from the flux**.

## Lesson for general BH

- **Count flux at fixed points and ends per link.** In Houghton groups an integer flux obstructs higher finiteness
  because it sits on germs at fixed ends, over a locally finite base, with boundedly many ends per descending link.
- **Germ extensions of V-type groups have neither.** Their base is `F_∞`, their flux sits only on transfer germs, and their singular points
  are dense and unlimited. So wall fluxes of hyperbolic hosts are bookkeeping for the germ complex, not obstructions.
- **The finiteness question for bounded hosts is one combinatorial lemma:** high connectivity of bounded-sum joins,
  together with contractibility of the zero-sum part. For hyperbolic inputs, the genuine frontier stays at
  exponential activity.
