---
rg: 2
id: sft-isolated-points-are-finite-state-across-finite-edge-groups
kind: claim
title: Across a finite edge group, an isolated point of an SFT is a finite-state recursion of isolated points of SFTs over the vertex groups; so over virtually free groups relative seeds are exactly the Stallings seeds, and for finitely presented groups CAP for relative seeds reduces to one-ended groups
requires:
  - relative-seeds-glue-graphs-of-groups-into-class-c
distinct_from:
  relative-seeds-glue-graphs-of-groups-into-class-c: that glues relative seeds of vertex groups into relative seeds of the fundamental group (construction); this is the converse over finite edge groups, where every isolated point of every SFT over the fundamental group decomposes into isolated points over the vertex groups (structure), with no rigidity assumed.
  heisenberg-rigid-seed-certifies-only-the-malcev-normal-form: that shows the seeds built from locally finite splittings certify only Britton normal forms; this bounds every isolated point of every SFT over a group split over finite subgroups, not only the ones built by gluing.
  finite-type-e3-prime-hosts-carry-complexity-in-units: that says the complexity of a finite-type E3′ host is that of its unit groupoid; this is the analogue for seeds, where the complexity of an isolated point is that of its one-ended pieces.
  relative-seeds-on-free-groups-have-fg-stabilizers: that proves the free-group case of item 3 (finitely generated stabilizers, regular membership), landed shortly before by bh-g1-universal-point; this extends it to virtually free groups and to every splitting over a finite subgroup, with the complexity reduction of items 1, 2 and 4.
  relative-seeds-over-free-products-have-finite-ropes: that proves the branch lemma across trivial edge stabilizers and its consequences over P * Q, landed shortly before by bh-invent-15; this is the same mechanism across finite edge groups, stated as a finite-state recursion of vertex-group isolated points, with the reduction of CAP to one-ended groups.---

**ESTABLISHED** by `sft-isolated-points-finite-edge-groups-proof` (lane bh-g3-topfree, 2026-09-18;
elementary lane proof, not reviewed; no priority claimed). Anisimov–Seifert and Dunwoody accessibility
are recalled, not re-read. The free-group and free-product cases were found independently the same hour
(`relative-seeds-on-free-groups-have-fg-stabilizers`, `relative-seeds-over-free-products-have-finite-ropes`).

## Setting

- `A` is finitely generated and `Y ⊆ Σ^A` is an SFT, with `A` acting by `(η·y)(γ) = y(η^(-1)γ)`.
- A point `y_* ∈ Y` is **isolated** if `{y ∈ Y : y|_W = y_*|_W} = {y_*}` for some finite `W ⊆ A`. This
  is condition (RS1) of `relative-seeds-glue-graphs-of-groups-into-class-c`, with `C = Stab(y_*)`.
  Neither rigidity nor orbit density is assumed anywhere below.
- **Evaluating** `y_*` means computing `y_*(g)` from a word for `g`.
- `A` **splits over a finite subgroup** if `A = B_1 *_K B_2` or `A = B *_K` (an HNN extension along
  `K`, `φ(K)` with `K` finite), where the vertex groups are finitely generated.

## Statement

1. **Decomposition.** Suppose `A` splits over a finite subgroup, and `y_* ∈ Y` is isolated. Then there are
   finitely many SFTs `Y_1, ..., Y_m` over the vertex groups, and isolated points `z_j ∈ Y_j`, such that
   `y_*` is evaluated by a finite-state recursion along Bass–Serre normal forms:
   - the recursion reads one syllable `b ∈ B_v` at a time;
   - at each syllable it evaluates one `z_j` at `≤ |K| + 1` elements `b k`;
   - it moves to the next piece by a fixed finite table.
2. **Complexity.** So evaluating `y_*`, and deciding membership in `C = Stab(y_*)`, takes polynomial
   time given oracles for the word problems of the vertex groups and for evaluating the `z_j`. The same
   holds for every finite graph of groups with finite edge groups, by induction on the number of edges.
3. **Virtually free groups.** If `A` is virtually free, then every isolated point of every SFT over `A`
   has a finitely generated stabilizer. On a free subgroup of finite index, `y_*` is computed by a
   finite automaton on reduced words, and the reduced words of the stabilizer form a regular language.
   With corollary (a) of `relative-seeds-glue-graphs-of-groups-into-class-c`:
   `(F_n, C) ∈ 𝓡 ⟺ (F_n, C)` satisfies (RS1) for some SFT `⟺ C` is finitely generated.
4. **CAP for relative seeds reduces to one-ended groups.** Let `A` be finitely presented. By Dunwoody's
   accessibility, `A` is the fundamental group of a finite graph of groups with finite edge groups whose
   vertex groups are finite or one-ended. By 2, membership in the stabilizer of any isolated point of any
   SFT over `A` is polynomial-time reducible to the word problems of the one-ended vertex groups and to
   evaluating finitely many isolated points of SFTs over them.

## Remarks

- **Free products with `Z` add nothing.** The (SEED) gate glues seeds over `Λ_0 * Z`. By 1, such a
  glued seed is a finite-state recursion of seeds over `Λ_0` and `Z`. So all of its computation happens
  on `Λ_0`, and the one-ended content of the input's overgroup carries it.
- **Where computation can cross.** Item 1 fails for infinite edge groups: the interface between two
  pieces is then an infinite coset. That is where the Higman–Clapham towers of
  `relative-seeds-glue-graphs-of-groups-into-class-c` put their hard associated subgroups.
- **Smallest one-ended test.** `F_2 × F_2` is one-ended, and its Mihailova fiber products
  `C_Q = {(u, v) : π(u) = π(v)}`, for `π: F_2 -> Q` with `Q` finitely presented, have membership exactly
  as hard as the word problem of `Q`. The coset space `(F_2 × F_2)/C_Q` is `Q` with the two-sided action
  `(a, b)·q = π(a) q π(b)^(-1)`. So a hard relative seed there is a locally forced labelling of `Q`
  that sees left and right multiplication at once. Whether one exists for a `Q` with hard word problem
  is open.
- **Compression collapses light cones.** This is the dynamical counterpart of 1, for points that are
  not isolated. Over a regular tree with an end `ξ`, let a layer be computed away from `ξ`: each value is
  a function of the layer within horospherical distance `r` of the parent. Then the value at `v` depends
  only on the layer below one ancestor, on a cap of `(d−1)^⌊r/2⌋` vertices. So the layer is a finite
  automaton transported away from `ξ`, with no room for a tape (proof, §5).

## Lesson for general BH

**Finite cuts are finite-state.** A forced configuration crosses a finite interface only through
finitely many interface patterns, because the far side of a finite cut is constrained by the cut alone
(branch independence). So seeds cannot compute across ends.

**Consequences.**
- Over virtually free groups, the relative seeds are exactly the Stallings seeds of finitely generated
  subgroups. The finite-state character of every seed recorded so far is a theorem there, not an
  accident.
- For finitely presented groups, CAP for relative seeds is a question about one-ended groups.

**The missing coding.** A non-finite-state rigid compression coding must compute either inside a
one-ended group or across an infinite edge interface. The first concrete target is `F_2 × F_2` with a
Mihailova fiber product.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS.** I checked `sft-isolated-points-finite-edge-groups-proof` step by step. Lane
bh-g3-topfree's "finite cuts are finite-state" is a clean and useful structure theorem.
- **§0.** The higher-block recoding is correct. Paths inside `B_r` transport the overlap
  consistency.
- **§1.** Both cut properties are correct:
  - amalgam: both pieces of a point off `I(f)` lie on one side;
  - HNN: by Britton, the `t`-edges realizing `f` are exactly `gk — gkt`.
- **§2.** (BI) and (UE) are correct. One wording note: in the amalgam case the outside neighbours of
  `A_f^+` lie in the parent piece, not in `I(f) ∖ A_f^+`, which is empty. The proof does not use that
  sentence; "keep `y_*` elsewhere" suffices.
- **§3.** The piece SFTs `Y_v^L`, the uniqueness in (P1) via (UE), and the completion in (P2) are
  correct. Each point lies in one interface per piece, so every edge constraint is accounted for.
  There are finitely many types `(v, τ, p)`.
- **§4.** Checked:
  - the recursion along normal forms;
  - `C = {h : y_*(hw) = y_*(w) for all w ∈ W}`;
  - over `Z`, eventual periodicity (by (UE) at cut points);
  - the automaton composition on reduced words;
  - the regular language, then Anisimov–Seifert, then `C ∩ F` finitely generated of finite index.

  Item 4 uses Dunwoody accessibility for finitely presented groups.
- **§5.** The cap recursion `D_ρ(a_{ρ+m}(v))` is correct.
- **Consistency.** Item 3 agrees with, and extends to virtually free groups, the free case of
  `relative-seeds-on-free-groups-have-fg-stabilizers` (bh-g1-universal-point), refereed alongside.
