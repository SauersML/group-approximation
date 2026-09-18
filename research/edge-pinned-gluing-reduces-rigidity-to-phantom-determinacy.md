---
rg: 2
id: edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy
kind: claim
title: Core edges with small stabilizers can be pinned by seeds of the edge group, which gives an isolated point with stabilizer exactly S; rigidity then holds when the vertex configuration is a continuous function of the pins, and fails to follow exactly at anchorless "phantom" cosets
requires:
  - core-marked-gluing-of-relative-seeds
distinct_from:
  core-marked-gluing-of-relative-seeds: that assumes full stabilizers on core edges (FE), where core edges are finite sums of atoms; this drops (FE), pins the edge-group twist with a seed of the edge group, and isolates the one extra hypothesis rigidity needs.
  fate-couplings-are-rigid-only-along-directed-implication-chains: that shows proximity alone does not propagate commutation; this locates where the tower's gluing meets that obstruction, namely at anchorless double cosets of limit configurations.
---

**Status.** Lane bh-invent-03, 2026-09-18; elementary lane proof, not reviewed.
- Items 1–2 and item 3 under (PC) are **ESTABLISHED**.
- Rigidity **without** (PC) is **OPEN**.
- Requested by bh-invent-14 for the B_1 re-split (seed-tower board), where (FE) fails on all three stable-letter pairs.

## Setting

As in `core-marked-gluing-of-relative-seeds` ((K0), (KV), (E)), but with (FE) replaced by two hypotheses:
- (DM) **definable double cosets.** For each core datum `(p, ε, k)` there is a clopen `U ⊆ Y_p` with
  `x ∈ S'_p a_k C_ε ⟺ x^(-1).y_*^p ∈ U`. It is then read locally at every element `x`.
- (P) **pins.** `(C_ε, S''_k) ∈ 𝓡`, with `S''_k = a_k^(-1) S'_p a_k ∩ C_ε` (the core edge stabilizer, pulled
  back). Call the relative seed the *pin* `P_k`. Its alphabet lives on left `C_ε`-cosets, via right multiplication
  by generators of `C_ε`.

**The pin layer.** Each core vertex carries its `Y_p` layer and, on every `U`-marked coset `xC_ε`, a pin
configuration. The rules:
- (A) **anchoring:** "pin seed at `x`" iff "`Y_p` seed at `x a_k^(-1)`";
- (X) **exact pin transport across the edge:** pin letters at `xc` iff reverse-pin letters at `xc t_ε`;
- (N) **neighbour anchoring:** "reverse-pin seed at `x'`" iff "neighbour `Y_q` seed at `x' b^(-1)`".

The remaining rules (type transport, pointers for out vertices, exclusivity) are those of the core-marked theorem,
with "core edge" read through `U`.

## Statement

1. **(RS1).** The seed "class `p_0`, seed at `1`" has a single-point cylinder, and `Stab(y_*) = S`.
2. **(RS2).** `Y` is the orbit closure of `y_*`.
3. **(RS3) under (PC).** Assume (PC), **phantom determinacy**: for every core datum, on the orbit closure `Ŷ_p` of the
   vertex-plus-pin configuration, every vertex letter is a continuous function of the pin configuration on each
   `U`-marked coset. Then `Y` is `D`-quantum rigid for large `D`.

## Proof

**1. Isolation.** At a core vertex with a seeded configuration, a `U`-marked coset has exactly one anchor
`s a_k S''_k`-class, by (DM). By (A), its pin is the unique seeded pin configuration at that anchor. By (X), the
pin crosses the edge. By (N), it pins the neighbour's `Y_q` configuration. So the core is pinned from the base,
exactly as in the core-marked proof.
- Consistency holds because the `S`-equivariant configuration exists.
- The stabilizer argument is unchanged: a stabilizing `g` maps the base to a core vertex of the same class and
  configuration, so `g ∈ S`.

**2. Density.** The classification of limit points is that of the core-marked proof, plus **phantom cosets**:
`U`-marked cosets whose anchor has escaped, carrying seedless pins.
- They are limits of anchors `a_n → ∞` along the coset.
- Since `U` is clopen, every limit configuration keeps the mark.

**3. Rigidity under (PC).**
- **Vertex letters are pin polynomials.** By (PC) and compactness, each vertex letter at `x'` is a Boolean
  function of finitely many pin letters on any fixed `U`-marked coset. That identity holds in `LC(Ŷ_p)`. The
  vertex-plus-pin family on one coset is commutative: `Ŷ_p` is a finite-type recoding of `Y_p` under (PC), and
  the F-trick applies. So the identity holds for operators. Hence on a core edge, every letter at `v` and every
  letter at `w` is a polynomial in the **shared** pin letters of the edge coset, identified by (X).
- **Shared pin letters commute.** They form one rigid family for `P_k`.
- **Letters across a core edge commute.** They are polynomials in commuting shared letters.
- **The path argument.** Along a path, the decomposition `1 = B_i + C_i + Γ_i` and the monotone chains
  `C_i ≤ C_(i+1)` of the core-marked proof carry over.
  - `Γ_i` is now the `U`-event, and is the same operator at both endpoints, by (X) and (A).
  - The atom step there is replaced by the polynomial step above.

  So letters at any two vertices commute. ∎

## Corollary: locally finite anchors

Suppose every core edge group `C_ε` has **finite index** in `V_(o(ε))`, so the tree is locally finite at the core,
and (DM) holds. Then the edge-pinned gluing is rigid, with no pin layer.

**Proof.**
- **Recoding.** Fix a right transversal `F` of `C_ε`, with `V = ⊔_(f ∈ F) C_ε f`. Recode `Y_p` by the `V`-equivariant
  block map `y ↦ (x ↦ y|_(xF))`. This is a conjugacy, so rigidity, (RS1) and (RS2) are unchanged.
- **Restriction is injective.** After recoding, the restriction of a configuration to any coset `xC_ε` determines
  it, since `xC_εF = V`. It does so on the **whole** orbit closure.
- **(PC).** A continuous bijection from a compact space onto a Hausdorff one is a homeomorphism. So the vertex
  configuration is a continuous function of its restriction to each coset.
- **Pins are restrictions.** Take the pin on a core coset to be the restriction itself. It is a relative seed for
  `(C_ε, a_k^(-1) S'_p a_k ∩ C_ε)`: its `C_ε`-stabilizer is computed through injectivity. Finite-index restriction
  keeps it of finite type and rigid, by the quasi-isometry argument of the induction lemma of 5deee0184.
- **Rules.** Rules (A) and (N) collapse to one: the recoded vertex configurations of the two endpoints agree along
  the edge coset through `φ_ε`. Item 3 then applies. ∎

**Scope.** This is the coordinator's "locally finite anchors" form, and it covers bh-invent-14's `(Z_J, F(a))`
(6aa2688ed), whose m-adic phases supply (DM).
- **Free edge groups.** Σ and Y have infinite index in their vertex groups, so this corollary does not apply there.
  Phantom determinacy (PC) must be proved directly, or the route changed to (FE).

## Where (PC) fails, and why that is the tower's one obstruction

Without (FE), a core edge is a clopen `U`-event rather than a finite sum of atoms.
- **Phantom cosets carry free data.** By compactness, `U` also marks cosets of limit configurations whose anchor
  has escaped. There the pin is seedless and can carry free data: the sign `±` of `C_Z` pins, or an end of a free
  edge group.
- **What (PC) says.** That free data is determined by the vertex configuration.
- **Without (PC).** Two phantom cosets can carry independent free data, linked only by proximity, and
  `fate-couplings-are-rigid-only-along-directed-implication-chains` (2e723c93e) shows proximity forces nothing.
- **Three faces of one obstruction:**
  - the unterminated `m`-adic sheets of `modular-machine-mortality-at-infinity-is-uniform` (d03fdfb06), at gate 4;
  - the "one sign" left in bh-invent-14's `(Z_J, F(a))` landing (6aa2688ed);
  - (PC) here.

**Examples.**
- **(PC) holds.** `V = Z^2`, `S' = ⟨y⟩`, `C_ε = ⟨x⟩`, with `C_Z` pins on rows. The vertex configuration (one point
  × `C_Z`) *is* the pin, including at `+^Z` and `−^Z`.
- **(FE) is the case `S'' = C_ε`.** Pins are one-point, there are no phantoms, and this recovers the core-marked
  theorem.

**For the tower.** Two ways forward, in order of preference.
- **(i) Re-route so that core edges are (FE).** Enlarge the subgroup by the edge groups, e.g. use
  `⟨Q, Σ⟩` in place of `Q = F(a) * ⟨t⟩`, and check that the next rung still accepts the enlarged subgroup.
- **(ii) Verify (PC) for the actual pins.** For `(Z_J, F(a))`, (PC) asks whether the `C_Z` sign on a phantom
  `⟨x⟩`-coset is a continuous function of the vertex's `m`-adic phases. bh-invent-14's reduction "tree data plus one
  sign" is exactly this.

## Lesson for general BH

The remaining gates of the seed tower share one mechanism: **free data at infinity**.
- **Where it appears.** Rigidity is automatic wherever limit configurations carry no data beyond what directed
  implications propagate: atoms, (FE) edges, locally finite trees. It breaks exactly where a clopen mark survives
  into a limit without its anchor.
- **Its three forms.** Phantom cosets (infinite-index edge stabilizers), unterminated m-adic sheets (machine
  rungs), and incomparable fates (couplings).
- **One design rule for all three.** Every mark must either come with its anchor, as with atoms and (FE), or
  determine its free data continuously, as (PC) requires.
