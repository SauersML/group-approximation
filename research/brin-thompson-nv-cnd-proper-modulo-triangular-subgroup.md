---
rg: 2
id: brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
kind: claim
title: "For n >= 2 the Brin-Thompson group nV carries a cnd function proper modulo the triangular subgroup T_n"
distinct_from:
  brin-thompson-nv-cnd-proper-on-triangular-subgroup: that is the fibre half of the split (properness on T_n); this is the transversal half (properness on the coset space nV/T_n)
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that proves the cubical version of this statement is false; this asks for an arbitrary cnd function
---

**OPEN.** No proof and no refutation is recorded.
- The cubical candidates are dead, by `brin-thompson-nv-no-cubical-action-proper-mod-triangular`.
- Weighted and non-cubical cocycles are unexplored.
- The refutation test of the gq-nv-obstruct attempt has not been carried out. That test is a subset with
  relative property (T) not contained in finitely many cosets of `V^n`.

**Statement.** Let `n ≥ 2` and let `T_n ≤ nV` be the triangular subgroup of
`brin-thompson-triangular-subgroup-is-undistorted`. There is a conditionally negative definite
function `ψ_1` on `nV` such that each sublevel set `{ψ_1 ≤ R}` lies in finitely many left cosets of `T_n`.

**Role.** This is the transversal prerequisite of `brin-thompson-nv-a-t-menable-via-triangular-split`.
It is necessary for the Haagerup property of `nV`, by (1) ⇒ (2) of
`haagerup-splits-as-coset-plus-subgroup-properness`.

**Forced shape.** By `brin-thompson-nv-no-cubical-action-proper-mod-triangular`, any such `ψ_1` has
`ψ_1(f^N) → ∞` and `ψ_1(f^N) = O(log^8 N)` on the Callard–Salo element, and is not a finite sum of
wall counts.

## Attempts

- 2026-09-17 (swarm-0917-w4-nv-cocycle). *Cubical transversal: dead.* The natural candidate is a
  Farley-type wall count measuring how far `g` is from triangular: walls from brick charts whose
  projections to the first `k` coordinates are not charts of `C^k`. Every commensurating action
  fails by `brin-thompson-nv-no-cubical-action-proper-mod-triangular`.
- *Weighted wall counts.* Sums `Σ_j w_j |gA_j Δ A_j|` with infinitely many commensurated sets
  escape the bounded-or-linear dichotomy. The difficulty is that `nV` acts transitively on proper
  brick charts with a fixed shape, so natural invariant weights are constant on large families and
  the series diverges. A convergent weighting would have to use the scale of the charts.
  Unexplored.
- *Relative coarse geometry.* A necessary condition is that the coset space `nV/T_n`, with the
  quotient of a word metric, has growth compatible with a Hilbert-space compression along
  `⟨f⟩`. No computation yet.
- 2026-09-17 (lane gq-nv-obstruct). *Strength, and a refutation test.* Route
  `kazhdan-finiteness-in-nv-via-cnd-transversal`. Apply `ψ_1` after the coordinate-permutation
  automorphisms of `nV`: the triangular subgroups of the `n` orders starting with each coordinate
  intersect in `V^n`. Two consequences:
  - This claim alone already makes every Kazhdan subgroup of `nV` finite (by Farley for `V^n`), with
    no fibre half. So it answers Zaremsky 2.19(a), (c) and (d) with "no". It is exactly as strong as
    a cnd function proper modulo `V^n`.
  - It is refuted by any subset of `nV` with relative property (T) that is not contained in finitely
    many left cosets of `V^n`. Such a subset would also refute the Haagerup property of `nV`.
  So this half is no easier than finiteness of Kazhdan subgroups. Constructing `ψ_1` needs a
  non-cubical cocycle that is unbounded but polylogarithmic on the Callard–Salo element; not attempted.
- **2026-09-18 (swarm-0917-w7-w7-nv-pull): witnesses carried by finite clopen cuts (die;
  class-kill).**
  - R1 implies Problem B(Z), which implies a `C_0` witness for `C(C,Z) ⋊ V ≤ 2V` with no
    `1_C`-invariant vectors. Established `clopen-extractable-spectra-carry-no-almost-invariant-vectors`
    to constrain where that witness's spectral law can live.
  - Suppose the `C(C,Z)`-spectrum lies on a `V`-invariant character set with an equivariant Borel map
    to probabilities on proper clopens. Then the spectral part has norm at most `1032ε`, where `ε` is
    the defect under `h_1, h_2, h_3`.
  - This kills "random finite cut, Haar below" witnesses: every law absolutely continuous to a
    countable sum of Haar extensions over nontrivial finite clopen algebras.
  - **Invariant:** the maximal-pure leaf partition.
  - **Where every member dies:**
    - Shallow clopens have mass at most `46ε`.
    - On deep clopens, leaf-uniform Lebesgue averaging commutes with the three moves.
    - The averaged probability on `C` is then paradoxical.
  - **Surviving:** characters whose natural cut is infinite (random open or nowhere-dense closed
    sets with infinitely many leaves). There no normalizable equivariant leaf weighting exists.
  - A positive R1 must place its witnesses there.
- **2026-09-18 (swarm-0917-w8-w8-nv-pull): V-fixed-point witnesses (die; class-kill).**
  - R1 implies Problem B(Z), which needs a cnd function on `C(C,Z) ⋊ V ≤ 2V` that is unbounded on
    `Z·1_C`. Established `cantor-central-v-elliptic-witnesses-die`: every cnd function on
    `C(C,Z) ⋊ V` that is bounded on `V` is bounded on `Z·1_C`.
  - *Class.* Affine actions with a `V`-fixed point. Equivalently, `V`-invariant cnd functions
    `ψ(f) = Φ(Im f)` on `C(C,Z)`, or exactly `V`-invariant spectral laws. The class includes the
    additive split `ψ_A + ψ_V∘p`, `L^α` constructions whose norm depends on the image set, and
    `E g(X(f))` for a random real homomorphism `X` with invariant law (such an `X` is `0` a.s.).
  - **Invariant:** the exchangeable phases `χ(1_{[1^{i-1}0]})`, whose partial sums all have one law.
  - **Where every member dies:** de Finetti's directing measure `ν`. Cesàro averaging gives
    `φ(k·1_U) = P(ν̂(k) = 1) ≥ P(ν = δ_0) = φ(1_U)`, hence `ψ(k·1_C) ≤ 4ψ(1_{[0]})`.
  - **Surviving:** witnesses unbounded on `V` whose spectral laws are almost invariant with
    non-vanishing defect. The argument needs exchangeability under all of `S_n` for every `n`, and
    it has no quantitative version under a fixed finite set.
