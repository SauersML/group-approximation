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
- **ESTABLISHED (lane proof, bh-finf-hyp, 2026-09-19; Referee bh-ref-q12 2026-09-19: items 1, 2 and 4 PASS
  with repairs, and item 4's proof is replaced by a simpler one; item 3 is a heuristic, not a theorem):** items
  1–4.
- **OPEN:** the link half of Lemma 5, now Conjecture C of `level-set-join-complexes-are-highly-connected`. The
  contractibility half is proved there. Item 5a for `c = 0` is withdrawn (Referee section).
- No computation was run.

## Setting

- This is `torsion-defect-costs-nothing-in-bhm-germ-complexes`, with defect group `⟨Δ⟩ ⊆ H_0(G_Σ)` possibly
  infinite. For the right-angled pentagon RSG its image in the coarse `H_0 ≅ Z` is `⟨x⟩`, and each
  reflection has fluxes `+x, +x, −x, −x` there (the true `⟨Δ⟩` may also contain torsion; repair 1) (`gq-bh-finf-hyp-pentagon-defect-class.md`).
- **The per-point bound.** `(L)_p/(B)_p` is finite, so each singular point carries finitely many B-germ classes.
  Since there are finitely many B-orbits of singular points, `|d| ≤ δ_max` for all singular germs.

## 1. The flux lives only on transfer germs; germ stabilizers see none

- For `p` fixed by `g` and `h`, the cocycle rule gives `d_{gh}(p) = d_g(p) + d_h(p)`. So
  `ψ_p : Stab_L(p) → ⟨Δ⟩`, `g ↦ d_g(p)`, is a character of the germ group `(L)_p`.
- `ψ_p` vanishes on `(B)_p` (canonical germs), and `(B)_p` has finite index in `(L)_p`. So `ψ_p` factors through a
  finite group, and **`ψ_p = 0` whenever `⟨Δ⟩` is torsion-free** (for example `Z` for the pentagon).
- Hence the pentagon's `±x` fluxes sit on **transfer germs**, i.e. germs at points the element moves. The
  reflection exchanges its paired singular points, which is consistent with this.
- **Global characters.** For a B-orbit `O` of singular points, `φ_O(g) = Σ_{p∈O} d_g(p)` is a homomorphism on
  `Stab_L(O)` (repair 2: an element of `L` need not map B-orbits to B-orbits, so no finite-index claim is made).
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
  the number of ends available to one descending link (bounded for Houghton, unbounded here). So one known obstruction mechanism is absent. This is **analysis, not a theorem** (referee): it proves no
  finiteness statement. This is consistent with BBMZ's finite
  presentation.

## 4. The zero-sum-completable germ complex is the orbit of non-singular cells (proof replaced per referee)

- A partial portrait is completable iff it is `portrait(ℓ)` with some points hidden, for some `ℓ ∈ L`
  (parent, Step 1).
- Hiding commutes with the action, so `K_0` is `L`-invariant. Moreover `ℓ·γ` is non-singular: its germs are
  trivial and its hidden set is `ℓ(M)`.
- So **`K_0` is exactly the `L`-orbit of BHM's non-singular cells**, and BHM Propositions 2.5, 2.6 and 2.8 apply
  verbatim:
  - `K_{0,≤n}` has finitely many orbits of cells, by oligomorphy;
  - cell stabilizers are commensurable with `SingFix_L(M,M')`, which is `F_∞`.
- This works for an infinite defect group too. The earlier invariance argument was wrong: total defect is not
  invariant for partial portraits.

## 5. What remains

- By item 4, every descending link is isomorphic to one at a non-singular vertex, where the revealed total is 0.
- **Contractibility of `K_0` is now proved** by a nerve argument, in `level-set-join-complexes-are-highly-connected`.
- **The link half** is stated there as **Conjecture C**, through the inflation formula. It says that the pure
  complexes generated by level sets of integer sums are `(h−3)`-connected.
- **Item 5a.** The earlier description of the case `c = 0` ("removes only top simplices") is **withdrawn**. It is
  wrong, because the completability constraint also removes lower faces. The cases `c = h` and `c = h−1` stand.

**Consequence.** Conjecture C, together with items 2 and 4 and the contractibility of `K_0`, and Bestvina–Brady gives `F_∞` for every bounded full contracting
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

## Referee (bh-ref-q12, 2026-09-19): items 1, 2, 4 PASS with repairs; item 3 heuristic; 5a partly wrong

**Item 1 (no flux at fixed points): correct, with two repairs.**
- `ψ_p` is a homomorphism on `Stab_L(p)`, it is a germ invariant, and it vanishes on `(B)_p`.
- Finite index gives `g^m ∈ (B)_p` for some `m ≥ 1`, so `ψ_p` is always **torsion-valued**, and it is 0 when
  `⟨Δ⟩` is torsion-free.
- **Repair 1.** "`⟨Δ⟩ = ⟨x⟩ ≅ Z` for the pentagon" is not established. Only the image of `⟨Δ⟩` in the coarse
  `H_0 ≅ Z` is computed (`gq-bh-finf-hyp-pentagon-defect-class.md`). The true `⟨Δ⟩` may also contain torsion in
  the kernel of `H_0(true) → H_0(coarse)`.
  - What is established is that fixed-point germs carry no **infinite-order** flux. That is all item 2 uses.
- **Repair 2.** `φ_O` is a homomorphism on `Stab_L(O)`. But "finite-index subgroup preserving each orbit" is
  unjustified: an element of `L` need not map `B`-orbits (tail classes) to `B`-orbits.

**Item 2: correct.**
- The stabilizers of the cells of `K_0` are handled by BHM Propositions 2.5 and 2.8, and so are `F_∞`. These use
  only `|(L)_p : (B)_p| < ∞`.
- So `k = 0` is true in the torsion-free case, but it is not needed for the finiteness of stabilizers.

**Item 3 is a heuristic, not a theorem.**
- The facts quoted are correct: Houghton's `H_n` is `F_(n−1)` and not `F_n` (Brown), and `FSym` is not finitely
  generated.
- But "no Houghton-type obstruction arises, at any `n`" only says that one known mechanism is absent. It proves no
  finiteness statement. Grade it as analysis.

**Item 4 (cocompactness): the conclusion is correct; the stated reason is wrong and is replaced.**
- **The stated reason is wrong.** Total defect is not `L`-invariant for partial portraits; hidden points absorb
  germs, as in the parent's referee section.
- **The correct reason.** A partial portrait is completable iff it is `portrait(ℓ)` with some points hidden, for
  some `ℓ ∈ L` (parent Step 1). Hiding commutes with the action, so `K_0` is `L`-invariant.
- **Moreover `ℓ·γ` is non-singular.** It has trivial germs and hidden set `ℓ(M)`. So
  **`K_0` is exactly the `L`-orbit of BHM's non-singular cells.**
- BHM Propositions 2.5, 2.6 and 2.8 then apply verbatim:
  - `K_(0,≤n)` has finitely many orbits of cells, by oligomorphy;
  - cell stabilizers are commensurable with `SingFix_L(M,M')`, which is `F_∞`.
- The bound `|c| ≤ nδ_max` and the parent's count are not needed. They also cover an infinite defect group.

**Lemma 5 and 5a.**
- **Where the problem lives.** Every vertex of `K_0` is `L`-equivalent to a non-singular one. So all descending
  links are isomorphic to links at non-singular vertices, where the revealed total is 0.
- **What Lemma 5 needs.** High connectivity, depending only on `h`, of the subcomplex of the join
  `∗_(p∈M) Bgerm(L,p)` of revealings `S ⊆ M` whose defect sum `σ` lies in `−Σ_(p∈M∖S) D_p`. Here each
  `Bgerm(L,p)` is finite and contains the trivial germ. Contractibility of `K_0`, or directly high connectivity of
  `K_(0,≤n)`, is also needed. Both are open.
- **5a, cases `c = h` and `c = h − 1`: descriptions and connectivity check.** Attaching cones along
  `(h−3)`-connected joins preserves `(h−2)`-connectivity.
- **5a, case `c = 0`: wrong as stated.**
  - Take `δ_max = 1` and `D_p = {−1, 0, 1}`. The constraint `|σ| ≤ h − |S|` also removes non-top simplices once
    `|S| > h/2`. For example, `h = 4` with three revealed germs of defect `+1` has `σ = 3 > 1`.
  - With one-signed `D_p`, far more is removed.
  - Since `c = 0` is the only case that matters (above), Lemma 5 is open in its essential case.

**Literature.** No source found for `F_∞` of bounded full contracting RSGs with a non-torsion defect (searches
09-19, as in `bounded-defect-free-full-contracting-rsgs-are-f-infinity`).

**Verdict: PASS with repairs** for items 1, 2 and 4 (item 4's proof replaced). Item 3 is a heuristic. Item 5a is
correct for `c = h` and `c = h−1` and wrong for `c = 0`, which is the case that matters. `F_∞` for the pentagon RSG
remains open.
