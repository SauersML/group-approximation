---
rg: 2
id: bi-lipschitz-splittings-add-one-exponential-to-the-word-problem
kind: claim
title: A finite graph of groups whose edge maps are bi-Lipschitz raises word-problem complexity by at most one exponential; so locally finite splittings, and graphs of free and free abelian groups, certify only elementary word problems, and CAP holds on them with the class ELEMENTARY
distinct_from:
  bs12-rigid-seed-is-its-normal-form: that measures one rung and asks whether "compressed WP in P" survives finite-index HNN extensions; this answers the question behind it by an explicit, compression-free bound per splitting level, and shows compression is not the right invariant.
  baumslag-gersten-seed-forcing-length-is-non-elementary: that is a splitting over an exponentially distorted edge, where this bound fails, although the word problem stays polynomial; this is the undistorted side of the same dichotomy.
  relative-seeds-glue-graphs-of-groups-into-class-c: that puts graphs of groups into 𝒞; this bounds what the resulting seeds can certify when the edge maps are bi-Lipschitz.
---

**ESTABLISHED (lane proof, bh-g1-universal-point, 2026-09-18; elementary, not independently reviewed).**

## Statement

Let `Λ = π_1(𝔾)` for a finite graph of finitely generated groups.
- **Edge maps.** For each oriented edge `e` there are an edge group `C_e ≤ V_{ι(e)}` and an injection `φ_e : C_e → V_{τ(e)}`.
- **Hypotheses.**
  - **(BL) bi-Lipschitz edges:** there is `K` with `|φ_e^{±1}(c)| ≤ K|c|` in the word metrics of the vertex
    groups. This holds when every `C_e` and every `φ_e(C_e)` is undistorted in its vertex group. In particular it
    holds for finite-index edge groups, for f.g. subgroups of free groups, and for subgroups of `Z^m`.
  - **(M) constructive membership:** given a word `g` over `V_u`, one can decide `g ∈ C_e` and, if so, find a
    `C_e`-word of length `≤ K|g|`. The time for this is `M(|g|)`.
  - `T(n)` bounds the word problems of the vertex groups.

Then `WP(Λ)` is decidable in time
`O(n²K^n) + n·M(nK^n) + T(nK^n)`.

**Corollaries.**
- **(a) Per-level cost.** If `T`, `M` ∈ `DTIME(exp_k(poly))`, then `WP(Λ)` ∈ `DTIME(exp_{k+1}(poly))`. Here
  `exp_0(n) = n` and `exp_{k+1}(n) = 2^{exp_k(n)}`.
- **(b) The locally finite closure is elementary.** Let `𝒞_lf` be the closure of `{finite groups, Z}` under `×`,
  `*` and finite graphs of groups with finite-index edge groups. These are the members of `𝒞` given by
  `locally-finite-splittings-preserve-rigid-sft-compactifications` and its corollaries.
  - A group of splitting depth `k` has `WP ∈ DTIME(exp_{k+1}(poly))`.
  - `×` and `*` cost only a polynomial.
  - The other vertex groups of a splitting are commensurable with the `𝒞`-vertex, so they cost only a linear
    Reidemeister–Schreier rewriting.
  - So every group in `𝒞_lf` has elementary word problem.
- **(c) Graphs of free and free abelian groups.** For vertex groups free or free abelian with f.g. edge groups
  (`relative-seeds-glue-graphs-of-groups-into-class-c`), (BL) and (M) hold with `M` polynomial. This uses Stallings
  foldings, and linear algebra over `Z`. So `WP(Λ) ∈ EXP`.
- **(d) CAP on this part of 𝒞.** CAP holds on `𝒞_lf`, and on depth-one graphs of free and free abelian groups,
  with the fixed class ELEMENTARY.
  - Some decidable groups have non-elementary word problems. Any fp group containing one of them has a
    word problem at least as hard (standard).
  - Such inputs therefore never embed in these groups.
  - So none of these seeds can serve (SEED) for all inputs. A seed tower built only from bi-Lipschitz splittings
    can never refute CAP.

## Proof

Write a word of length `n` in normal-form shape `g_0 x_1 g_1 x_2 ⋯ x_m g_m`. Each `g_i` is a word over one vertex
group, and each `x_i` is a letter of the graph (a stable letter or an edge crossing), so `m ≤ n`.

**Britton reduction.** A pinch is a subword `x_i g_i x_{i+1}` where
- `x_{i+1}` crosses the edge `e` back, and
- `g_i ∈ C_e`.

It is replaced by `φ_e(g_i)`, which is then concatenated with its neighbours `g_{i−1}`, `g_{i+1}` in the vertex
group on the other side.

**Correctness.** By Britton's lemma, or the reduced-form theorem for graphs of groups (Serre, recalled):
- a word with `m ≥ 1` and no pinch represents a non-trivial element;
- if `m = 0`, then `w = 1` iff `g_0 = 1` in its vertex group.

Pinches may be performed in any order.

**Cost.**
- **Lengths.** A pinch multiplies the length of the pinched piece by at most `K`, by (M) and (BL). Enlarge `K` to absorb the rewriting constant of (M). There are at
  most `n/2` pinches, so every piece has length at most `nK^n` throughout.
- **Membership tests.** Each test costs `M(nK^n)`. After a pinch, only the two neighbouring junctions need
  re-testing, so the number of tests is `O(n)`.
- **Final check.** At most one call to a vertex word problem, on a word of length `≤ nK^n`.
- **Rewriting.** Concatenation, and the finite rewriting of `φ_e` on generators, cost `O(nK^n)` per pinch.

This gives the bound. ∎

For (b), finite-index edge groups give (BL) with `K` = the maximal Schreier-rewriting constant. (M) is linear:
run the coset table of `V_u/C_e`, then Reidemeister–Schreier rewriting. The induction is on splitting depth.

## The question from the BS(1,2) rung

`bs12-rigid-seed-is-its-normal-form` asked whether "compressed WP in P" is preserved by finite-index HNN
extensions.

**Status.** Not settled here, and not needed.
- **The first case is already unknown.** For `A = Z` it asks whether `CWP(BS(1,2)) ∈ P`. What is proved here is
  `CWP(BS(1,2)) ∈ coRP`.
  - Compute `s_X` exactly, and `q_X mod p` for a random prime `p` of `m + O(1)` bits, using
    `q_{XY} = q_X + 2^{s_X} q_Y`.
  - A non-zero `q·2^{2^m}` has at most `2^{m+2}` prime factors, so a random `p` detects it with probability
    `≥ 1 − 2^{−5}`.
  - Deterministic P would need a zero test for integers built by `+` and `×2^s`, with carries across
    exponentially many digits. The swarm has no such test.
- **Compression is the wrong invariant for seeds.** The explicit bound above needs no compression, and it is what
  bounds certification. The distinction that matters is distortion of the edge maps, not the compressed word
  problem.

## The dichotomy for seed towers

A pinch costs the distortion `Δ_e(n) = max{|φ_e^{±1}(c)| : |c| ≤ n}` of its edge. Nested pinches iterate it.
- **Bi-Lipschitz edges.** `Δ` is linear, so each level costs one exponential. The whole tower is elementary.
- **Distorted edges.**
  - An example is Baumslag–Gersten: `⟨a⟩ → ⟨b⟩` in `BS(1,2)`, where `Δ(n) ≈ 2^n`.
  - Here `n`-fold iteration gives towers of height `≈ n`, which is the non-elementary forcing length of
    `baumslag-gersten-seed-forcing-length-is-non-elementary`.
  - Yet `WP(BG) ∈ P` (Myasnikov–Ushakov–Won, recalled). So distortion is necessary for non-elementary
    certification, but not sufficient.

## Lesson for general BH

- **Distortion is the currency.** What a seed tower can certify is bounded by the iterated distortion of its edge
  maps. Rigidity, the seed and the tree cost nothing here.
- **Bi-Lipschitz splittings are elementary.** Every locally finite splitting, and every graph of free or free
  abelian groups, adds at most one exponential per level. So these towers stay inside ELEMENTARY and cannot
  refute CAP.
- **What ¬CAP needs.** A counterexample needs edges whose distortion iterates non-elementarily, as in the
  Baumslag–Gersten mechanism. It also needs a way to make that distortion compute, and not merely compress:
  Baumslag–Gersten shows that huge distortion alone still leaves a polynomial word problem.
- **The concrete target.** The CAP-relevant rung is a seeded HNN tower over *distorted* edges whose pinches
  simulate a machine, in the style of Sapir–Birget–Rips or Clapham. Relative seeds over distorted subgroups are the
  missing tool.
