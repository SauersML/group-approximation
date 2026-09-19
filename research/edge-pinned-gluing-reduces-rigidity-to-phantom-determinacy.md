---
rg: 2
id: edge-pinned-gluing-reduces-rigidity-to-phantom-determinacy
kind: claim
title: Without full edge stabilizers, a core edge glues when both vertex seeds induce the same clopen, expansive compactification of the edge group; the glued SFT is then a rigid relative seed with stabilizer S, and without this matching the orbit closure fails even for index-one edges
distinct_from:
  core-marked-gluing-of-relative-seeds: that assumes full stabilizers on core edges (FE), where each vertex seed induces the one-point compactification of the edge group; this allows any edge stabilizer, and replaces (FE) by matching of the induced compactifications.
  fate-couplings-are-rigid-only-along-directed-implication-chains: that shows proximity alone does not propagate commutation; here the only couplings used are directed implications (pointers) and exact identities (shared traces).
---

**ESTABLISHED** by the proof below (lane bh-invent-03, 2026-09-19; elementary lane proof, not reviewed; no priority
claimed). Notation, (L0), (L1), atoms, domination and the F-trick are as in `relative-seeds-glue-graphs-of-groups-proof`
and `core-marked-gluing-of-relative-seeds`.

**Correction.** This supersedes the version landed in 8d6acdcd0. That version had two errors.
- **(RS2).** Its proof ignored mixed limit configurations.
- **Its corollary.** It said finite-index ("locally finite") core edges glue with no extra hypothesis. The example in
  §4 refutes that already at index one.

Requested by bh-invent-14 for the B_1 re-split, where (FE) fails on every stable-letter pair.

## Setting

`𝔾`, `Λ = π_1(𝔾)`, the tree `T`, `S ≤ Λ` and its core `K` are as in `core-marked-gluing-of-relative-seeds`, with
(K0), (KV) and (E), but **not** (FE). For a core datum `(p, ε, k)`, write:
- `a_k`, so that the core edges of that type at the class-`p` vertex are the cosets in `S'_p a_k C_ε`;
- `(q, ε̄, k')` for the reverse datum, and `b ∈ Λ` for the element carrying the genuine configuration across;
- `O_k := cl(C_ε · a_k^(-1).y_*^p) ⊆ Y_p`, the **compactification of the edge group `C_ε` induced by the vertex
  seed**.

**Hypotheses on each core datum.**
- (DM) **Clopen marks.** There is a clopen `U_k ⊆ Y_p` with `x ∈ S'_p a_k C_ε ⟺ x^(-1).y_*^p ∈ U_k`.
  - Then `U_k = O_k`: `U_k` is open and meets the dense orbit exactly in `C_ε a_k^(-1).y_*^p`.
  - So `O_k` is clopen and `C_ε`-invariant.
- (EX) **Expansive.** `C_ε ↷ O_k` is expansive. Equivalently, there is a `C_ε`-equivariant continuous injection
  `τ_k : O_k -> Σ_k^(C_ε)`, the **trace**. By compactness it is a sliding block code, read on the edge coset.
- (M) **Matching.** Transport `O_(k')` to a `C_ε`-system through `φ_ε` and the translation by `b`. The `C_ε`-orbit map
  `c.a_k^(-1).y_*^p ↦ c.(genuine neighbour point)` then extends to an equivariant homeomorphism
  `Ψ_k : O_k -> O_(k')`.

(EX) is needed on one side only: `τ_(k') := τ_k ∘ Ψ_k^(-1)` is a trace for the other side.

## Statement

Under (K0), (KV), (E), (DM), (EX) and (M), define the SFT `Y` over `Λ` as the SFT of the core-marked theorem with two
changes:
- **Core-edge rule.** "Core edge of datum `k`" is read at `x` as `x^(-1).y ∈ U_k`, and the neighbour must mark
  the same coset with datum `k'`.
- **(TR) Traces.** On every marked edge coset, the two endpoint traces agree letter by letter:
  `τ_k(v-side) = τ_(k')(w-side)`.

Then `Y` is a rigid relative seed for `(Λ, S)`:
- (RS1) the seed cylinder is one point `y_*`, with `Stab(y_*) = S`;
- (RS2) `Y` is the orbit closure of `y_*`;
- (RS3) `Y` is `D`-quantum rigid for large `D`, over every field over which the vertex and edge seeds are rigid.

**Special cases.**
- **(FE).** If `a_k C_ε a_k^(-1) ⊆ S'_p`, then `O_k` is one point, and (DM), (EX), (M) are trivial. This recovers
  `core-marked-gluing-of-relative-seeds`.
- **Finite-index edges.** If `[V : C_ε] < ∞`, then (EX) is automatic, because a finite-index subgroup of an expansive
  action is expansive. (DM) and (M) are genuine conditions, and §4 shows they can fail.

## Proof

**Operators.** Let `(E)` be a `D`-family. For a vertex `v`, `𝒜_v` is the commutative algebra of letters at `v` (as
in the core-marked proof).
- **Marks.** For a core edge `f` at `v`, let `Γ_f` be the sum over data of the mark events. By the core-edge rule and
  (L1), `Γ_f` is the same operator in `𝒜_v` and in `𝒜_w`.
- **Traces.** Each trace symbol event `[τ(y)(c) = σ]·Γ_f` is a clopen pattern event on a bounded window. By (TR) and
  (L1), it too is the same operator on both sides.
- **Pointers.** `B_f` ("`v` points along `f`") and `C_f` ("`w` points along `f`") are atoms of `𝒜_v` and of `𝒜_w`
  respectively.
- **Exclusivity.** `B_f + Γ_f + C_f = 1`. So all three lie in `𝒜_v ∩ 𝒜_w`.

**Step 1 (letters are trace polynomials on marked edges).** Let `X ∈ 𝒜_v` be a letter.
- On `O_k`, `X` is a continuous function of the configuration.
- By (EX) and compactness, `X|_(O_k)` factors through `τ_k` and depends on finitely many trace coordinates. So
  `X·Γ_f^(k) = h(trace events)·Γ_f^(k)` in `LC(Y_p)`, with `h` a Boolean polynomial.
- The commutative family at `v` obeys the forbidden patterns of `Y_p`, so it represents `LC(Y_p)` (F-trick). Hence
  this identity holds for the operators.
- The trace events and `Γ_f` lie in `𝒜_w`. Therefore **`X Γ_f ∈ 𝒜_w`**.

**Step 2 (induction on distance).** Claim: `𝒜_(v_0)` and `𝒜_(v_m)` commute for every tree path `v_0, …, v_m` with
edges `f_i`.
- `m = 0`: `𝒜_(v_0)` is commutative.
- **Monotone chain.** For `m ≥ 1`, write `B_i, Γ_i, C_i` for the events of `f_i`. Then `C_i ≤ C_(i+1)`: if `v_i`
  points back along `f_i`, it is out, so it neither points along `f_(i+1)` nor marks it. Exclusivity on `f_(i+1)`
  then gives `C_(i+1)`.
- **Decomposition.** Let `X ∈ 𝒜_(v_0)` be an idempotent. Write `X = XB_1 + XΓ_1 + XC_1`, a sum of commuting pieces.
  - `XΓ_1 ∈ 𝒜_(v_1)`, by Step 1. It commutes with `𝒜_(v_m)` by induction on the shorter path `v_1, …, v_m`.
  - `XB_1 ∈ {0, B_1}`, since `B_1` is an atom of `𝒜_(v_0)`. Also `B_1 = 1 − Γ_1 − C_1 ∈ 𝒜_(v_1)`, so it commutes by
    induction.
  - `XC_1 ≤ C_1 ≤ C_m`, and `C_m` is an atom of `𝒜_(v_m)`. So it commutes, by domination.

  So `X` commutes with `𝒜_(v_m)`.

Coordinates at one site commute by Q1, so all letters commute. This proves (RS3).

**(RS1).** Take the seed "class `p_0`, seed at `1`".
- **Core vertices.** Each marked edge of a genuine vertex carries its genuine trace. The neighbour's configuration
  lies in `O_(k')`, where `τ_(k')` is injective, so the neighbour is pinned. By connectedness, all of `K` is pinned.
- **Out vertices.** An unmarked edge at a core vertex must be pointed along by its other endpoint. So every vertex
  off `K` is out and points toward `K`, with its pointer configuration forced.
- **Stabilizer.** It is `S`, by the argument of the core-marked proof.

**(RS2).** Let `y ∈ Y`.
- **Orientation.** Out vertices have out-degree at most 1; a seedless one is an *out-sink*. Core vertices point
  nowhere. So, as in 5deee0184, `y` has exactly one of three things:
  - a connected **core component** `K'` of marked edges;
  - an out-sink;
  - an end.

  Two of them would force out-degree 2 somewhere on the path between them. The out-sink and end cases are
  approximated exactly as in 5deee0184, by moving `K` far beyond the sink's escaping coset or out to the end.
- **Approximation.** Otherwise fix `v ∈ K'` with configuration `z = lim g_n.y_*^p` in `Y_p`.
  - Marks are clopen, so on any finite subtree the marked edges of `g_n.y_*` and of `y` eventually agree.
  - Across each marked edge, the neighbour's configuration is `Ψ(·)` of the previous one: in `y` by (TR) and
    injectivity, in the translates by construction.
  - `Ψ` is continuous, so the configurations agree on the finite subtree in the limit, and the pointers toward it
    agree as well.
  - So `y` is a limit of translates of `y_*`. ∎

## 4. Why (M) cannot be dropped, even at index one

Let `Λ = Z² *_(⟨x⟩) Z²`, with vertex groups `⟨x, y⟩` and `⟨x, z⟩`. Take `S = 1` and let the core be one edge.
- **Seeds.** Put `Y_V = C_Z(x) × C_Z(y)`. Put `Y_W = P(x) × C_Z(z)`, where `P` is an SFT compactification of `Z` with
  period-2 tails.
- **Other hypotheses hold.** (DM) holds: the edge coset is the seed row. (EX) holds.
- **Different compactifications.** The induced compactifications of `⟨x⟩` are `Z ∪ {±∞}` and `Z` with four limit
  points. They are not homeomorphic over the orbit map, so (M) fails.
- **Mixed points.** The rule "seed at `s` ⟺ seed at `s`" alone allows mixed limits, such as `+^Z` on the `V` side with
  a `P`-tail of either parity, or with a left tail. These are not limits of translates, so (RS2) fails.

The fix is to choose the vertex seeds so that they induce the same compactification of the edge group.

## Lesson for general BH

**Gluing sees the edge groups through the vertex seeds.** Each vertex seed induces a compactification `O` of every
core edge group, the orbit closure along the edge coset.
- **The gluing condition.** The two endpoints must induce the **same** compactification, and it must be clopen and
  expansive, i.e. readable by a local trace. That is (DM), (EX) and (M).
- **Earlier cases.** Full edge stabilizers (FE) are the case where this compactification is a point. The phantom
  cosets of the earlier draft are its boundary points.
- **What does not matter.** Local finiteness of the anchors is not the operative condition. Matching is, and it
  already fails at index one.
- **For the seed tower.** On the B_1 pairs with free edge groups Σ and Y, bh-invent-14 should choose J's seeds so that
  they restrict to Σ's own free-group seed on each marked coset. Free-group seeds are finite-state
  (`relative-seeds-on-free-groups-have-fg-stabilizers`), so (DM), (EX) and (M) become finite checks.
