---
rg: 2
id: baumslag-gersten-seed-forcing-length-is-non-elementary
kind: claim
title: The Baumslag–Gersten group lies in 𝒞, via a rigid "real-cut" relative seed for (BS(1,2), ⟨b⟩) and relative-seed gluing; the explicit glued seed has non-elementary forcing length (at least a tower of height about log n) although the word problem is polynomial, so forcing length does not measure certified complexity
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
  - locally-finite-splittings-preserve-rigid-sft-compactifications
  - heisenberg-rigid-seed-certifies-only-the-malcev-normal-form
distinct_from:
  heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: that is rung 1b, where forcing length is quadratic and equals the distortion of the centre; this is rung 1c's distortion test, where forcing length is non-elementary while the word problem stays polynomial.
  relative-seeds-glue-graphs-of-groups-into-class-c: that is the gluing theorem; this supplies the two rigid relative seeds that the Baumslag–Gersten splitting needs, so the theorem applies.
---

**ESTABLISHED** (lane proof, bh-emitter-a, 2026-09-18; elementary; not reviewed). The one unproved item is the
expected polynomial bound on evaluation (§4), which is labeled as a sketch.

## Setting

- **The groups.** `V = BS(1,2) = ⟨a, b | b a b^{-1} = a²⟩ ≅ Z[1/2] ⋊ Z`.
  - Coordinates: `a = (1, 0)`, `b = (0, 1)`, with `(r, k)(s, m) = (r + 2^k s, k + m)`.
  - Right multiplication by `a` is `(r, k) ↦ (r + 2^k, k)`, and by `b` it is `(r, k) ↦ (r, k + 1)`.
- `BG = ⟨a, t | a^{a^t} = a²⟩ = ⟨V, t | t a t^{-1} = b⟩`, an HNN extension of `V` along `⟨a⟩ → ⟨b⟩`.
- **Distortion.** `b^k a b^{-k} = a^{2^k}` and `b^k = t a^k t^{-1}`, so `|a^{2^k}| ≤ 2|a^k| + 5` in `BG`.
  - Put `N_0 = 1` and `N_{j+1} = 2^{N_j}`. Then `|a^{N_j}| ≤ 6·2^j`.
  - So `⟨a⟩` has distortion at least `tower(log₂ n − 3)`.
- **Word problem.** `WP(BG)` is polynomial time (Myasnikov–Ushakov–Won, J. Algebra 345 (2011), power circuits;
  recalled, not re-read).
- **`C_Z` notation.** `σ(r)` is `+` for `r < 0`, `*` for `r = 0`, and `−` for `r > 0`.

## 1. The two rigid relative seeds on `V`

**`(V, ⟨a⟩) ∈ 𝓡`.** `⟨a⟩` is the vertex group of the splitting `V = ⟨a⟩ *_{a ↦ a²}`, whose edge groups have
finite index. Statement 1 of the gluing theorem (second bullet) applies.
- The seed `y_a` is the pointer field toward the sink vertex `⟨a⟩` of the tree `T_V`.

**`(V, ⟨b⟩) ∈ 𝓡`: the real-cut seed `y_R`.**
- **The SFT `Y_R`.** Alphabet `{+, *, −}`.
  - (Rb) The letter at `h` equals the letter at `hb`.
  - (Ra) Along `a`, the pairs `(ℓ(h), ℓ(ha))` must lie in `{++, +*, +−, *−, −−}`.
  - The seed is `*` at `1`.
- **(RS1).** The forced point is `y_R(r, k) = σ(r)`.
  - (Rb) spreads `*` over `(0, k) = b^k`.
  - (Ra) at level `k` forces `σ` on `2^k Z`.
  - Any `(r, k)` equals `(r, k − m)` by (Rb), and `r ∈ 2^{k−m} Z` for large `m`.
  - Stabilizer: `(g.y_R)(r, k) = σ(r − s)` for `g = (s, m)`, so `Stab(y_R) = {s = 0} = ⟨b⟩`.
- **(RS2).** Points of `Y_R` are exactly Dedekind cuts of `Z[1/2]` with at most one `*`.
  - By (Rb), a point depends only on `r`.
  - For `r < r'`, take `k` with `r' − r ∈ 2^k N`. Chaining (Ra) at level `k` shows the labels do not increase
    in the order `+ > * > −`, and a `*` is followed only by `−`.
  - Every such cut is a limit of translates, which are the cuts at dyadic `s` with `*` at `s`. Irrational
    cuts, one-sided dyadic cuts and the constants `±` are limits of those.
- **(RS3), rigidity for every `D ≥ 1` over every field.** Take a `D`-family `E_ℓ(·)`.
  - By exact transport along (Rb), `E_ℓ(r, k) = E_ℓ(r)` for all `k`.
  - For `r < r'`, the level-`k` chain gives: `E_−(r) ≤ E_−(r')`, `E_+(r') ≤ E_+(r)`, `E_*(r) ≤ E_−(r')`
    and `E_*(r') ≤ E_+(r)`.
    - Each step uses two forbidden patterns at distance 1, commutation at distance 1, and transitivity of
      `≤`.
  - So the `E_+(r)` form a chain and commute.
  - Each `E_*(r)` lies below, or is orthogonal to, every idempotent at another site. For example, if `r < r'`,
    then `E_*(r) E_+(r') = E_*(r) E_−(r') E_+(r') = 0`.
  - Hence all site idempotents commute, and `Y_R` is rigid. `∎`
- **Reading.** `y_R` is the real cut at `0` of the affine action on `R`: the second boundary of `BS(1,2)`,
  not the tree. Its forcing is logarithmic. `a^{2^m}` is reached through `b^m`, one `a`-step, and `b^{-m}`,
  in `2m + 1` steps.

## 2. `BG ∈ 𝒞`

Both edge images `⟨a⟩`, `⟨b⟩ ⊂ V` have rigid relative seeds, and `V ∈ 𝒞`. So the gluing theorem gives
`BG ∈ 𝒞`.

**An explicit glued seed `Y_BG`.** It follows the gluing pattern. At the vertex `hV` of the Bass–Serre tree of
`BG`:
- the `t`-edges are the cosets `c⟨b⟩`, since `h b^k t = h t a^k`;
- the `t^{-1}`-edges are the cosets `c⟨a⟩`.

Each coset carries one of three types:
- `S`: the sink, carrying the seed of `V` from `locally-finite-splittings-preserve-rigid-sft-compactifications`
  (a `T_V`-sink `⟨a⟩` with `C_Z` along `a`);
- `P_t`: a `y_R`-layer, whose `*`-coset `c⟨b⟩` is the exit;
- `P_{t^{-1}}`: a `y_a`-layer, whose sink coset is the exit.

The rule (Xt): `h` is `P_t` and `*` iff `ht` is not (`P_{t^{-1}}` and `sink`).
- **(C1).** The seed is type `S` with the `V`-seed letter at `1`.
  - For `h ∈ V`, (Xt) forces every neighbor's exit coset, and each layer is then forced by its (RS1).
  - The argument continues outward.
  - The stabilizer fixes the unique sink and the `V`-seed, so it is trivial.

## 3. Forcing length of `Y_BG` is non-elementary

- **Where the `±` values come from.** The `±` values of `C_Z` on the sink line `⟨a⟩ ⊂ V` enter only the `C_Z`
  rules along `a`. The other rules mention types, pointers, `sink`, and `*` or `±` of the exit layers on
  other cosets.
- **The bound.** Under unit propagation, `−` at `a^m` follows only from `*` or `−` at `a^{m−1}`. So forcing
  `y_*(a^{N_j})` takes at least `N_j` steps, and the forcing length on `B_n` is at least `tower(log₂ n − 3)`.
- **Comparison.** `WP(BG)` is polynomial, so no elementary function of word-problem complexity bounds forcing
  length.
  - The exit layers `y_R` of the same seed force in logarithmic length.
  - So forcing length is a property of the design, not of the group.

## 4. What it certifies

- **Membership.** The relative seeds are membership oracles (statement 3 of the gluing theorem) for `⟨a⟩` and
  `⟨b⟩` in `Z[1/2] ⋊ Z`: a tree vertex and a real cut. Both are polynomial.
- **Evaluation.** `WP(BG) ≤ Eval(y_*)`.
  - We expect `Eval(y_*)` to be polynomial through power circuits, since every label is a sign, a parity or
    a tree position of a power-circuit normal form.
  - That is a sketch, not proved here.
- **Conclusion.** The seed encodes only easy memberships. The distortion shows up as forcing length, not as a
  certified hard function.

## Lesson for general BH

Distortion certifies nothing, and a second boundary can seed what a tree cannot.
- **The real-cut seed.** `⟨b⟩ ⊂ BS(1,2)` stabilizes no vertex, and the tree end it fixes is not isolated. The
  real line of the affine action gives it a rigid relative seed by monotone chains. So the Baumslag–Gersten
  group is in 𝒞.
- **Forcing length.** It is non-elementary for the natural glued seed and logarithmic for its exit layers,
  while `WP(BG)` is polynomial. It is a design-dependent upper bound, not a CAP invariant.
- **The CAP invariant.** It is the complexity of the membership oracles, so rung-1c tests need subgroups with
  hard membership.

## Referee (bh-ref-kourovka-a, 2026-09-18): PASS for BG ∈ 𝒞; §3 is a statement about the natural glued seed, and §4 is a sketch, as labeled

I checked §§1–3 against the definitions (RS1)–(RS3) and Statement 1 of
`relative-seeds-glue-graphs-of-groups-into-class-c`, which is refereed.

- **Setting.**
  - `ba = (2,1) = a²b`.
  - The distortion recurrence is `f(j+1) = 2f(j) + 5`, with `f(0) = 1`, so `f(j) = 6·2^j − 5`. This gives
    `|a^{N_j}| ≤ 6·2^j` and distortion at least `tower(⌊log₂ n − 3⌋)`.
- **`(V, ⟨a⟩) ∈ 𝓡`.** Both edge images `⟨a⟩`, `⟨a²⟩ ≤ ⟨a⟩` have finite index. Statement 1 (second
  bullet) applies.
- **The real-cut seed `Y_R`, (RS1).**
  - `σ` satisfies (Rb) and (Ra).
  - From `*` at `1`: (Rb) spreads it down the `b`-line. At level `k`, `*→−→−…` rightward and `…+←+←*`
    leftward force `σ` on `2^kZ`.
  - Every dyadic `r` is reached at a low enough level.
  - `(g.y_R)(r,k) = σ(r − s)` for `g = (s,m)`, so `Stab = ⟨b⟩`, and seeds sit exactly on `⟨b⟩`.
- **(RS2).**
  - Points depend only on `r`, and chaining (Ra) at a common level makes them monotone with at most
    one `*`. Conversely every such labelling satisfies the rules.
  - Limits of translates give every cut: non-dyadic cuts, both one-sided dyadic cuts (`s_n ↑ s` or
    `s_n ↓ s`) and both constants.
- **(RS3).**
  - The forbidden adjacent pairs `*+, **, −+, −*` give `E_−(h) ≤ E_−(ha)`, `E_*(h) ≤ E_−(ha)`,
    `E_+(ha) ≤ E_+(h)` and `E_*(ha) ≤ E_+(h)`. Transitivity of `≤` then yields commutation at all
    distances along the chains.
  - I also derived the cross cases the node leaves implicit.
    - `E_+(r)` commutes with `E_*(r')`: for `r < r'`, `E_*(r') ≤ E_+(r)`; for `r > r'`,
      `E_*(r') ≤ E_−(r) ⊥ E_+(r)`.
    - Then `E_−(r') = I − E_+(r') − E_*(r')` settles the rest.
  - So `Y_R` is rigid for every `D ≥ 1` over every field. `(V, ⟨b⟩) ∈ 𝓡`.
- **§2.** `BG` is the HNN extension of `V` along `⟨a⟩ → ⟨b⟩`, both images are in `𝓡`, and `V ∈ 𝒞`.
  So `BG ∈ 𝒞` by the gluing theorem. **Correct.**
- **§3.**
  - The lower bound is correct for unit propagation on the natural glued seed, given that the
    sink-line `C_Z` letters enter only the `C_Z` rules along `a`: `−` at `a^m` is forced only from
    `*`/`−` at `a^(m−1)`.
  - The explicit rule set of `Y_BG` is described, not written out, so this is checked only at that
    level.
  - The comparison with `WP(BG)` cites Myasnikov–Ushakov–Won 2011, recalled.
- **§4.** A sketch, as labeled.

This is independent of `baumslag-gersten-groups-lie-in-class-c` (the line-sink seed, d15e53b53), which
bh-ref-misc refereed separately (PASS, d1a5012563).
