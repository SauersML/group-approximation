---
rg: 2
id: linear-bouquet-recursions-ray-loop-and-contraction
kind: claim
title: For the 472 linear M_11 bouquet recursions the ray-loop subgroup at z^infinity is H = <S, T>, embedded in B wr F; G is contracting iff H is finite, and finite H makes G not finitely presented; b_1(G) = b_1(H), so the commuting cases with infinite H have H = Z x C_k, b_1(G) = 1 and are not FP_10 but pass every current fp obstruction
artifacts:
  - experiments/bouquet-ray-loop-2026-09-19/bouquets.py
  - experiments/bouquet-ray-loop-2026-09-19/ray_loop_hyp.py
  - experiments/bouquet-ray-loop-2026-09-19/ray_loop_hyp.out
  - experiments/bouquet-ray-loop-2026-09-19/nucleus.py
  - experiments/bouquet-ray-loop-2026-09-19/loops_B.py
  - experiments/bouquet-ray-loop-2026-09-19/loops_B.out
  - experiments/bouquet-ray-loop-2026-09-19/h_finite.py
  - experiments/bouquet-ray-loop-2026-09-19/h_inf.out
  - experiments/bouquet-ray-loop-2026-09-19/h_inf6.py
  - experiments/bouquet-ray-loop-2026-09-19/h_inf6.out
  - experiments/bouquet-ray-loop-2026-09-19/h_orders.py
  - experiments/bouquet-ray-loop-2026-09-19/h_orders.out
  - experiments/bouquet-ray-loop-2026-09-19/h_growth.py
  - experiments/bouquet-ray-loop-2026-09-19/h_growth.out
  - experiments/bouquet-ray-loop-2026-09-19/h_present.py
  - experiments/bouquet-ray-loop-2026-09-19/h_present.out
  - experiments/bouquet-ray-loop-2026-09-19/h_schreier.py
  - experiments/bouquet-ray-loop-2026-09-19/classify.py
  - experiments/bouquet-ray-loop-2026-09-19/classify.out
distinct_from:
  same-point-loop-recursions-reduce-to-loop-graph-words: that reduces the family to the 472 bouquet recursions and leaves them open; this decides the ray-loop hypotheses for them, identifies H, proves that contraction is equivalent to finite H, and sorts the 472 by it.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that proves the necessary condition H fp; here it is checked to hold trivially for the commuting survivors (H virtually Z), so a different obstruction is needed there.
  m11-odometer-free-host-is-not-finitely-presented: that kills R'' because its ray-loop group is L x C_5 with L non-fp; here no such factor appears in the commuting class, and the analogous retract tool (Lemma R) is stated for the non-commuting class but not applied.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that bounds b_1 of fp fully self-replicating groups by 1; this computes b_1 = 1 exactly for the commuting survivors by a germ character, which gives not FP_10 but leaves fp open.
---

**ESTABLISHED (unreviewed).** Proof: `linear-bouquet-recursions-ray-loop-and-contraction-proof`.
Items 1–3, 5 and 6 are proved by hand from finite data. Item 4's counts rest on exact
certificates, described in §4 and §6 of the proof. The classification of the undecided cases is
incomplete.

**Setting.** This is the bouquet class of `same-point-loop-recursions-reduce-to-loop-graph-words`
(its item 5), with the same notation.
- `M_11 = ⟨α, β⟩` acts on `X = {0, …, 10}`, and
  - `s = π_s (A s B, α, β, t, 1, …)`,
  - `t = π_t (C t D, 1, 1, 1, α, 1, …)`,

  with rooted words `A, B, C, D`, a common point `z = 0^{π_A^{-1}} = 0^{π_C^{-1}}`, and the
  loop words `S = A s B` and `T = C t D`.
- The roots `σ` and `τ` of `S` and `T` fix `z`, and `S|_z = S`, `T|_z = T`.
- `B = ⟨α, β, t⟩` is bounded. `F = ⟨σ, τ⟩`.
- `G = ⟨α, β, s, t⟩ = ⟨α, β, S, T⟩` is fully self-replicating: `G = G^X ⋊ M_11` (Lemma S there).

**Theorem.** For all 472 recursions:

1. **Hypotheses.** (Ω), (E) and (F) of `fp-self-similar-groups-have-fp-ray-loop-subgroups` hold
   at every constant ray.
   - The loop set at `z^∞` is `{S^{±1}, T^{±1}}`, and every other periodic ray has trivial
     loop group.
   - So the one loop condition is: **`G` fp ⇒ `H := ⟨S, T⟩` fp.**
2. **Embedding.** `h ↦ (π_h; (h|_y)_{y ≠ z})` embeds `H` in `B ≀_{X∖z} F`. It sends `S` and `T`
   to `σ(α@y_1, β@y_2, t@y_3)` and `τ(α@y_4)`, whose supports are disjoint.
   - If `σ = τ = 1` (40 cases), then `H = ⟨S⟩ × ⟨T⟩`.
3. **Lemma C.** Let `B` be contracting and let `S` fix `z` with `S|_z = S` and all other
   sections in `B`. Then `⟨B, S⟩` is contracting iff `⟨S, L⟩` is finite, where `L` is the set of
   `z^p`-loops in the nucleus of `B`.
   - Here `L = ⟨T⟩` in all 472 cases, by an exact nucleus certificate.
   - So **`G` is contracting iff `H` is finite.**
4. **Kills.** If `H` is finite, then `G` is contracting and regular branch over itself, hence
   not finitely presented (Bartholdi).
   - `H` is certified finite in 108 cases:
     - 27 commuting cases with `ord S < ∞`;
     - 81 cases by a presentation certificate: a GAP presentation of the level-2 image
       (50 cases) or of the level-3 image (31 cases), all of whose relators are trivial in
       `G`. Here `|H|` ranges over 13310, 212960, 3221020, 12884080, 206145280, 824581120
       and 103072640000.
5. **Germ character and commuting survivors.**
   - `b_1(G) = b_1(H) ≤ 1`. Moreover `b_1(G) = 1` iff `S` has infinite order in `H^{ab}`.
     Given `φ: H → Z`, the character is `λ(g) = Σ_{ξ ∈ X* z^∞} φ(c(g, ξ))`, where `c(g, ξ)`
     is the eventual section of `g` along `ξ`.
   - In the 20 commuting cases with `ord S = ∞`, `H ≅ Z × C_k`; for the 17 of them with
     `σ = τ = 1`, `H ≅ Z × C_11`.
   - So `H` is fp, `G` is not contracting, `b_1(G) = 1`, and `G` is **not `FP_10`** (item 3(d)
     of `fully-self-replicating-fp-infinity-groups-are-acyclic`, with `d = 11`).
   - **Finite presentability of these 20 is open.** No obstruction on the graph applies:
     - the loop condition holds;
     - `b_1 = 1` is the bound allowed for fp;
     - Bartholdi's theorem needs contraction;
     - `G` is amenable, since it has linear activity (Amir–Angel–Virág), so free-subgroup
       arguments are out.
6. **The rest.**
   - 212 non-commuting cases have `H` certified infinite, so `G` is not contracting. For them
     fp reduces to the fp of `H ≤ B ≀ F`.
   - **Lemma R.** Let `K = ker(H → F)`, `Q_y = p_y(K)` and `K_y = K ∩ B@y`. If
     `[Q_y : K_y] < ∞` and `G` is fp, then `Q_y` is fp, because `K_y` is a retract of a
     finite-index subgroup of `H`.
   - 132 cases are undecided: there is neither a finite certificate nor an infinite-order
     word of length at most 6. The screen `h_growth.py` (heuristic, used only for selection)
     splits them as follows:
     - in 58, the order of `S` grows from level 3 to level 4, so `H ≠ H_3`;
     - in 55, all short words have constant orders from level 3 on, but `|H_2| < |H_3|`.
       All 55 were queued for a level-3 certificate (900 s of GAP each, 2.5 h per worker).
       9 were attempted without a certificate, and 46 were not reached;
     - 19 have short-word orders constant from level 2. The level-2 certificate failed for
       all of them; at level 3, 9 failed and 10 were not reached.
     - "Failed" means GAP hit its limit or a relator of `H_n` is nontrivial in `G`. So these
       74 are the natural input for longer level-3 or level-4 runs.

| class | count | status |
|---|---|---|
| `H` finite, commuting | 27 | not fp (contracting) |
| `H` finite, presentation certificate | 81 | not fp (contracting) |
| `H ≅ Z × C_k`, commuting | 20 | not FP_10; **fp open** |
| `H` infinite, non-commuting | 212 | open (Lemma R is the tool) |
| undecided | 132 | open |

**What this does not do.**
- The family is not closed: 364 recursions remain open.
- No survivor is shown to be finitely presented. So there is no Boone–Higman embedding
  certificate from this family yet.

**Next step.** Decide one commuting survivor with `σ = τ = 1`, where `H = ⟨S⟩ × ⟨T⟩` is
explicit.
- Run the stable-relator computation (Lemma A of
  `same-point-loop-recursions-reduce-to-loop-graph-words`) in the Nielsen basis
  `α, β, S, T`. There (C'') is the only failing condition, and the loop relators are the
  commutator `[S, T]` and `T^{11}`.
- Alternatively, look for a non-finitely-presented retract of a finite-index subgroup, as in
  Lemma R.
