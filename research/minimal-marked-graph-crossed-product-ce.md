---
rg: 2
id: minimal-marked-graph-crossed-product-ce
kind: claim
title: Connes embeddability of the minimal marked graph's Clifford crossed product
distinct_from:
  invariant-graph-crossed-product-ce: that is the existential — SOME nondegenerate G-invariant graph containing the marked edge works — and its algebraic half was a search; this fixes the graph to be the minimal one, so it is a strictly stronger statement about a single named algebra, and the search is gone rather than postponed.
  kun-thom-clifford-crossed-product-ce: that fixes the COMPLETE anticommutation graph and asks for Connes embeddability of Cl(G/Gamma) crossed_product G; this fixes the smallest invariant graph containing the mark, whose lamp algebra is the AF twisted algebra rather than the full CAR algebra, so it is a different and strictly weaker analytic target.
  kun-thom-clifford-relative-wall: that asks for finite normalized-Hilbert--Schmidt walls in the complete-graph model; this asks for an exact embedding of one named algebra.
  bare-relative-wall-exists: that is the cheapest sufficient statement in the whole lane — a single non-commuting element of a relative commutant — with no Clifford sign and no graph in it; this is a full embeddability statement for a named crossed product and implies it.
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
---

Let `S_min` be the minimal marked orbital graph of the Kun--Thom Laurent pair
and `A_{S_min}` the twisted group von Neumann algebra of
`(F_2^{(X)}, b_{S_min})` at the central character `z ↦ −1`, with `G` permuting
the generators.  Prove that

```text
M_min = A_{S_min} ⋊ G
```

is Connes embeddable.

By `minimal-marked-graph-nondegenerate` the base `A_{S_min}` is the
hyperfinite `II₁` factor and `⟨z⟩` is the monolith of `W̃_{S_min}`, so this
claim discharges `invariant-graph-crossed-product-ce` outright, and through
`invariant-graph-ce-route` it answers `hyperlinear-nonsofic-group`.

**Finite-window form.**  Unwinding Connes embeddability of `M_min` through
microstates, the claim is: for every finite `E ⊆ G`, every finite `F ⊆ X`
and every `ε > 0` there is a matrix algebra `M_D(ℂ)` carrying

1. self-adjoint unitaries `W_x`, `x ∈ F`, with
   `W_xW_y = (−1)^{b(δ_x,δ_y)}W_yW_x`;
2. unitaries `U_g`, `g ∈ E`, with `‖U_gW_xU_g^* − W_{gx}‖₂ < ε` whenever
   `x, gx ∈ F`;
3. `‖U_gU_h − U_{gh}‖₂ < ε` whenever `g,h,gh ∈ E`;
4. the normalized traces of all words in these generators within `ε` of their
   values in `M_min` — in particular `0` on every nontrivial Weyl word.

**Item 1 and the trace part of item 4 are now free, exactly.**
`vertex-supported-symplectic-completion` builds them in a full matrix block
of dimension `D ≤ 2^{|F|}`, with the signs and the vanishing traces holding
on the nose rather than to within `ε`.  The whole content of the claim is
therefore items 2 and 3: **coherent** implementers.  That is the cleanest
current statement of what is left on the cheapest Kun--Thom Clifford branch.

## Attempts

- **Finite coordinate models — dead, twice.**  A finite `G`-set with charts at
  the mark cannot exist (`exact-models-cannot-separate-marked-pair`,
  `two-point-approximation-fails`, and for the published graph-wreath
  hypothesis `marked-graph-action-not-residually-finite`); and weakening the
  target from operator norm to normalized `2`-norm does not help, because a
  coordinate identification is already wrong by a full unit at second moments
  (`lamp-coordinate-collision-obstruction`).  Any surviving model is quantum
  and non-coordinate.
- **A canonical Clifford lift of the block's symplectic group — impossible.**
  `finite-clifford-symplectic-section-obstruction`: for binary blocks of
  qubit rank `≥ 2` the extension `1 → V_A → C(A) → Sp(V_A) → 1` does not
  split, so there is no multiplicative rule assigning Clifford elements to
  symplectic maps.  Items 2--3 must be met by asymptotic cancellation, never
  by an algebraic section.
- **Tensor padding to dilute a defect — dead.**  In an irreducible Clifford
  representation the normalized trace factorises, so tensoring a nontrivial
  local defect with the identity on a large complementary factor leaves its
  normalized contribution fixed; this is the same phenomenon as
  `wall-energy-amplification` and `additive-index-instability`.  The
  surviving dilution mechanism is a **direct sum** over many blocks, where
  the fraction of blocks carrying an effective defect can go to zero.
- **Finite-rank `G`-invariant completions — impossible**, by the finite-rank
  invariant-form no-go of `notes/NOTEPAD.md` together with
  `marked-double-coset-infinite-degree`.  The completions of
  `vertex-supported-symplectic-completion` are deliberately noninvariant, and
  this is why they do not contradict those no-gos.
- **Next concrete experiment (not yet run).**  Take a modest group window
  `E`, a lamp window `F`, and many independent completions sampled by
  `private-neighbour-density`; extend the tested partial symplectic maps on
  each block; record separately the `V_A`-valued Clifford factor set and the
  scalar Weil multiplier (`finite-clifford-symplectic-section-obstruction`);
  then ask whether a direct sum of blocks can drive the normalized defect mass
  of items 2--3 to zero while the exact lamp traces of item 4 are preserved.
  A persistent positive lower bound would be a new obstruction and would prune
  this lane sharply; decay in the polynomial degree would be the first
  positive evidence for the claim.
- **A design principle worth testing.**  The neighbour chart
  `a ↦ e_{qp}(a)h_{pq}Γ` of `minimal-marked-graph-private-neighbour` turns
  extra demands on a completion into conditions on a Laurent parameter.
  Whenever such a demand reduces to finitely many affine cosets of proper
  denominator ideals, high-degree abundance satisfies it simultaneously with
  privateness (`private-neighbour-density`).  Whether the Clifford cocycle
  conditions have that shape is open and is the cheapest thing to check
  first.
