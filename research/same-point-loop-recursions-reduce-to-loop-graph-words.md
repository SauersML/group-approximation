---
rg: 2
id: same-point-loop-recursions-reduce-to-loop-graph-words
kind: claim
title: For unit-weight recursions whose weight-preserving section cycles are self-loops, every stable relator is a cycle word of a finite loop graph on X, so finite presentation reduces to finitely many explicit power relators; this kills every same-point, generating-root recursion of a 62,500-member M_11 family except the bouquet class, where the rooted Nielsen move restores (A') and the question reduces to the ray-loop subgroup
artifacts:
  - experiments/loop-graph-screen-2026-09-18/loopgraph.py
  - experiments/loop-graph-screen-2026-09-18/same_point_screen.py
  - experiments/loop-graph-screen-2026-09-18/same_point_screen.out
  - experiments/loop-graph-screen-2026-09-18/bouquet_probe.py
  - experiments/loop-graph-screen-2026-09-18/bouquet_probe.out
distinct_from:
  pure-loop-self-replicating-groups-are-not-fp: that screen needs (A') and (C''), i.e. loops at distinct points or root images away from P; this handles two letters looping at the same point with root permutations generating P, where (A') and (C'') fail in the given basis, by computing Q^infinity exactly from the loop graph instead of assuming purity.
  m11-odometer-free-host-is-not-finitely-presented: that kills the single recursion R'' through its ray-loop group; this classifies a whole family, and shows the bouquet class (to which R'' belongs) is the only one not settled by stable relators.
  fp-self-similar-groups-have-fp-ray-loop-subgroups: that gives a necessary condition through loop subgroups at periodic rays; here that condition is what remains for the bouquet class, and every other class is decided without it.
---

**ESTABLISHED (unreviewed).** Proof: `same-point-loop-recursions-reduce-to-loop-graph-words-proof`.
Items 1–5 are proved by hand. Item 6 checks finite conditions, which the script decides
exactly. Infinite orders are certified by a finite graph argument, and finite orders are
certified by triviality of `w^o` together with non-triviality of each `w^{o/p}`.
Points are coded `0..10`, as in the script.

**Setting.** `P = M_11 = ⟨α, β⟩` acts on `X = {0, …, 10}`, and all actions are on the right.
`F` is free on the rooted letters `a ↦ α` and `e ↦ β` and on state letters `s`. A state letter
has a root permutation `π_s` and letter sections `s|_x`, which are words. `G = F/K` is the
resulting group of tree automorphisms. We assume:
- **(U)** every letter section contains at most one state letter;
- **(L1)** every directed cycle of the weight-preserving digraph (signed state letters, with an
  edge `s^ε → t^δ` when `t^δ` occurs in `s^ε|_x`) is a self-loop, and each letter has at
  most one self-loop.

Write the self-loop of `s` as `s|_{x_s} = A_s s B_s` with `A_s`, `B_s` rooted. Put
`ℓ_s = A_s s B_s`, `r_s = x_s^{π_A^{-1}}` and `w_s = x_s^{π_s π_B}`. The **loop graph**
`Γ_1` has vertex set `X` and one edge `r_s → w_s`, labelled `ℓ_s`, for each looping `s`.

`K` is the kernel of `F → G`. `Q^∞` is the stable part of the section closure of a finite
normal generating set, as in `m11-balanced-loop-host-is-not-finitely-presented`, item 1.
`T_k` is the map of the retract criterion in `pure-loop-self-replicating-groups-are-not-fp`,
item 1.

**Theorem.**

1. **(Lemma A, occurrence tracking.)** Assume (U). Let `v ∈ X^n` and let `u` be a reduced
   word. Then `u|_v = u` and `v^u = v` hold if and only if `u` is the label of a reduced closed
   path at `v` in the level-`n` loop graph `Δ_n`. The edges of `Δ_n` are the loop states
   `s^ε|_y = a s^ε b`, running from `y^{a^{-1}}` to `y^{s^ε b}`.
2. **(Loop graphs under (L1).)** `Δ_n` is `Γ_1` placed on the constant words `c^n`.
   - So `Fix_{c^n} = C_c := λ(π_1(Γ_1, c))`, and `Fix_v = 1` for every nonconstant `v`.
   - After the Nielsen move `s ↦ ℓ_s`, each `C_c` is a free factor of `F`. The tree edges
     and cycle words of its component form part of a basis.
   - **Every stable relator is a section of a relator in some `C_c`.** Each `q ∈ Q^∞` is a
     section of a relator `q''` on a cycle of the section digraph, `q''|_v = q''`. Since
     `q''` acts trivially, `v^{q''} = v`, so `q'' ∈ Fix_v ∩ K`, and `v` is constant.
3. **(Kills.)** Suppose every component of `Γ_1` has rank at most `1`.
   - (a) If every cycle word has infinite order, and `G` were finitely presented, then
     `Q^∞ = ∅`. Then `G` would be a retract of
     `F`, hence free, which is impossible because `G` has torsion. So `G` is **not
     finitely presented**. The same holds when `Γ_1` is a forest.
   - (b) Otherwise let `Q_E` be the section closure of `{w_c^{o_c}}`, where `w_c` runs over
     the cycle words of finite order `o_c`. Then `⟨⟨Q^∞⟩⟩ ⊆ ⟨⟨Q_E⟩⟩ ⊆ K`, and
     **`G` is finitely presented iff `T_k(K) ⊆ ⟨⟨Q_E⟩⟩` for some `k`.** These are finitely
     many explicit stable relators.
   - (c) **Kurosh with any number of factors.** Suppose `F` has a basis partitioned as
     `⊔ S_i`, every word of `Q_E` is conjugate into some `F(S_i)`, and every `ρ(F(S_i))` is
     proper in `G`. Then `G` is not finitely presented.
4. **(Proper images.)** `ρ(F(S_i))` is proper in each of these cases:
   - `S_i` is one letter;
   - `S_i` consists of rooted letters;
   - the root image of `S_i` is not `P`;
   - the section closure `L` of the letters used by `S_i` is bounded (every state letter in
     `L` has rooted non-loop sections), while `G` contains an unbounded letter. An
     unbounded letter is a looping `s` whose non-loop section contains a looping, non-rooted
     `t`. Such an `s` has at least `n` nontrivial sections at level `n`, while `⟨L⟩`
     consists of bounded automorphisms.
5. **(Same-point dichotomy; the premise is false for bouquets.)** Let `s` and `t` be the only
   state letters, both looping at the same point `x`. Either `Γ_1` has rank at most `1`,
   and items 3–4 apply, or `Γ_1` is a **bouquet**: `r_s = w_s = r_t = w_t = z`.
   - In the bouquet case, `π_{ℓ_s}` and `π_{ℓ_t}` both fix `z`, and `ℓ_s|_z = ℓ_s`,
     `ℓ_t|_z = ℓ_t`. So in the basis `{a, e, ℓ_s, ℓ_t}`, **(A') holds** (the state root
     image lies in `Stab(z) ≅ M_10`), but (C'') fails at `z`. This is the shape of `R''`.
   - `ℓ_s` and `ℓ_t` are their own eventual sections along the ray `z^∞`. So the ray-loop
     subgroup `H_{z^∞}` of `fp-self-similar-groups-have-fp-ray-loop-subgroups` contains
     `⟨ℓ_s, ℓ_t⟩`. Once that node's hypotheses (Ω), (E) and (F) are checked at `z^∞`,
     finite presentation of `G` forces `H_{z^∞}` to be finitely presented.
   - **Bounded kill.** If every state letter is bounded, `G` is a bounded automaton group,
     hence contracting. It is fully self-replicating, hence regular branch over itself. So
     it is not finitely presented, by Bartholdi as cited in
     `fully-self-replicating-tree-groups-give-fg-tits-hosts`. This holds in every class,
     bouquets included.
6. **(Screen.)** The family has
   - `s = π_s (A s B, α, β, [t], 1, …)` and `t = π_t (C t D, 1, 1, 1, α, 1, …)`;
   - `π_s, π_t` running over 8 short words in `α^{±1}, β^{±1}` with `⟨π_s, π_t⟩ = M_11`
     (50 pairs);
   - `A, B, C, D ∈ {1, α^{±1}, β^{±1}}`;
   - the section `s|_3 = t` either absent (bounded) or present (linear).

   Each member is fully self-replicating (Lemma S of the proof). Outcomes are in the table
   below.

| Class | Bounded family (31,250) | Linear family (31,250) |
|---|---|---|
| forest `Γ_1` | 20,640 not fp (contracting) | 20,640 not fp (`Q^∞ = ∅`) |
| rank one, all cycle words of infinite order | (in the next row) | 5,610 not fp (3a) |
| rank one, finite orders | 10,138 not fp (contracting) | 4,528 not fp (Kurosh 3c/4) |
| bouquet | 472 not fp (contracting) | **472 open** (item 5) |

   There is no survivor outside the bouquet class. The rank-one bounded count of 10,138
   includes both order types. As sanity checks of items 1–2, the script compares `Δ_2`
   with `Γ_1` for the whole linear family, and `Δ_2`, `Δ_3` for the calibration cases. It also
   checks `u|_c = u`, `c^u = c` for every cycle word. All of these checks passed.

   Calibration:
   - `R''` is the bouquet class.
   - `R'` is killed by 3c/4: `ord(b) = 55`, and `c` has infinite order.
   - `R_0` is bounded.
   - `R°` lies outside (L1), as it should.

**What this does not do.** The 472 linear bouquet recursions are not decided. For them,
every stable-relator obstruction in this node is silent. What remains is the ray-loop
subgroup at `z^∞`, which contains `⟨ℓ_s, ℓ_t⟩`, both loops fixing `z`. That is the
obstruction that killed `R''`. The expectation that two same-point loops with generating
root permutations break (A') and (C'') in every basis is false for this class: the rooted
Nielsen move `s ↦ ℓ_s` restores (A').

**Data for the bouquet class** (`bouquet_probe.out`, exact certificates as in item 6).
- `ℓ_t` always has finite order (11, 22 or 44), since `t` is bounded.
- `ℓ_s` has finite order (from 55 up to 77,440) in 390 cases, and infinite order in 82.
- `ℓ_s` and `ℓ_t` commute in 47 of the 472 cases.

The ray-loop subgroup is not computed here, so whether the `R''` pattern (`H ≅ L × C_5`
there) recurs is open. Deciding `H_{z^∞}` class by class is the next step.
