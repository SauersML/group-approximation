---
rg: 2
id: same-point-loop-recursions-reduce-to-loop-graph-words-proof
kind: route
title: Proof that under (U) and (L1) the stable relators are sections of loop-graph cycle words, that forests, infinite-order cycles and Kurosh-carried power relators are never finitely presented, and that the same-point M_11 screen leaves only the bouquet class
target: same-point-loop-recursions-reduce-to-loop-graph-words
requires:
  - pure-loop-self-replicating-groups-are-not-fp
  - m11-balanced-loop-host-is-not-finitely-presented
  - fully-self-replicating-tree-groups-give-fg-tits-hosts
  - fp-self-similar-groups-have-fp-ray-loop-subgroups
artifacts:
  - experiments/loop-graph-screen-2026-09-18/loopgraph.py
  - experiments/loop-graph-screen-2026-09-18/same_point_screen.py
  - experiments/loop-graph-screen-2026-09-18/same_point_screen.out
  - experiments/loop-graph-screen-2026-09-18/bouquet_probe.py
  - experiments/loop-graph-screen-2026-09-18/bouquet_probe.out
---

**Status: ESTABLISHED (unreviewed).** Items 1–5 are proved below by hand. Item 6 is a finite
computation, and its certificates are explained in §6. Notation is as in the claim. Words
are reduced words in `F`, and `u|_x` is the letterwise section, freely reduced. For a word
`g ∈ K` (so `g` acts trivially) and `y ∈ X^n` we use two identities:
- `(g^m)|_y = (g|_y)^m`;
- `(p g p^{-1})|_y = p|_y · g|_{y^p} · (p|_y)^{-1}`, which uses `(p^{-1})|_{y^p} = (p|_y)^{-1}`.

## 1. Lemma A

Write a reduced `u` as `r_0 s_1 r_1 ⋯ s_m r_m`, where the `s_i` are signed state letters and
the `r_i` are rooted words. Rooted words are nonempty except possibly at the ends and
between non-inverse state letters. Let `y_i = v^{r_0 s_1 ⋯ r_{i−1}} ∈ X^n` be the vertex
at which `s_i` is read. Rooted letters have trivial sections, so
`u|_v = red(s_1|_{y_1} ⋯ s_m|_{y_m})`.

**(⇒)** Suppose `u|_v = u` and `v^u = v`.
- By (U), each `s_i|_{y_i}` has at most one state letter. Reduction never creates state
  letters, and `u|_v = u` has `m` of them. So each `s_i|_{y_i}` has exactly one,
  `s_i|_{y_i} = a_i t_i b_i`, and no two of them cancel.
- The reduced form of `a_1 t_1 b_1 ⋯ a_m t_m b_m` is then
  `red(a_1) t_1 red(b_1 a_2) ⋯ t_m red(b_m)`. Comparing it with `u` gives `t_i = s_i`,
  `r_0 = red(a_1)`, `r_i = red(b_i a_{i+1})` and `r_m = red(b_m)`.
- So each `(s_i, y_i)` is a loop state, that is, an edge `e_i` from `ι_i = y_i^{a_i^{-1}}` to
  `o_i = y_i^{s_i b_i}`.
- The edges chain up:
  - `ι_1 = v^{r_0 a_1^{-1}} = v`;
  - `ι_{i+1} = y_i^{s_i r_i a_{i+1}^{-1}} = y_i^{s_i b_i} = o_i`;
  - `o_m = v^u = v`.
- The path is reduced. The inverse of the edge `s^ε|_y = a s^ε b` is the loop state
  `s^{−ε}|_{y^{s^ε}} = b^{-1} s^{−ε} a^{-1}`. So `e_{i+1} = e_i^{-1}` would give
  `s_{i+1} = s_i^{-1}` and `r_i = red(b_i b_i^{-1}) = 1`, and `u` would not be reduced.

**(⇐)** Let `e_1 ⋯ e_m` be a reduced closed path at `v` with labels `a_i s_i b_i`, and put
`u = red(∏ a_i s_i b_i)`.
- No `s_i` cancels. If `s_{i+1} = s_i^{-1}` with `b_i a_{i+1} = 1`, then `e_{i+1}` is a loop
  state of `s_i^{-1}` at `ι_{i+1}^{a_{i+1}} = o_i^{b_i^{-1}} = y_i^{s_i}`. A letter's
  section at a vertex is unique, so `e_{i+1} = e_i^{-1}`, a contradiction.
- Hence `u = red(a_1) s_1 red(b_1 a_2) ⋯`. By induction on `i`, the vertex at which `u` reads
  `s_i` is the vertex `y_i` of the loop state `e_i`. So `u|_v = red(∏ a_i s_i b_i) = u` and
  `v^u = o_m = v`.

The path is recovered from `u` and `v`, so `λ : π_1(Δ_n, v) → F` is injective, and
`Fix_v = λ(π_1(Δ_n, v))`.

## 2. Loop graphs under (L1)

**Loop states live on constant words.** A loop state `(s^ε, y)` with `|y| = n` gives a
closed walk of length `n` in the weight-preserving digraph: follow the state letter of
`s^ε|_{y_1 ⋯ y_j}`. Suppose a closed walk visits a vertex other than its start. Then it
contains a closed subwalk through two distinct vertices, and hence a simple cycle of length
at least `2`, which (L1) forbids. So every step is the unique self-loop of `s^ε`.

For `ε = +1` this reads as follows:
- `y_1 = x_s` and `s|_{x_s} = ℓ_s`;
- `ℓ_s|_y = s|_{y^{π_A}}` because `A` and `B` are rooted, so `y_j = r_s` for `j ≥ 2`;
- thus `ℓ_s|_{r_s} = ℓ_s` and `r_s^{π_{ℓ_s}} = w_s`, which gives `(r_s^m)^{ℓ_s} = w_s^m`.

So the edge of `(s, y)` runs from `y^{A^{-1}} = r_s^n` to
`y^{s B} = (x_s^{π_s π_B}, (r_s^{n−1})^{ℓ_s}) = w_s^n`, and it is labelled `ℓ_s`. The loop
states of `s^{-1}` are the inverse edges. Hence `Δ_n` is `Γ_1` on `{c^n}`, plus isolated
vertices, and item 1 gives `Fix_{c^n} = C_c` and `Fix_v = 1` for nonconstant `v`.

**Free factor.** `s = A^{-1} ℓ_s B^{-1}`, and `A`, `B` are rooted, so `{a, e, ℓ_s, …}` is a
basis. A component of `Γ_1` has pairwise distinct basis letters on its edges. Fix a
spanning tree with base vertex `c_0` and tree paths `p_c`. The cycle words are
`g_f = p_{ι(f)} ℓ_f p_{o(f)}^{-1}` for the non-tree edges `f`. Each `g_f` involves `ℓ_f`
once, together with tree letters only. So replacing each `ℓ_f` by `g_f` is a Nielsen
transformation, and `C_{c_0} = ⟨g_f⟩` is a free factor with `C_c = p_c^{-1} C_{c_0} p_c`.

**Stable relators.** Let `G = F/⟨⟨R⟩⟩` with `R` finite. By item 1 of
`m11-balanced-loop-host-is-not-finitely-presented`, the stable part
`Q^∞ = Q^{(k_0)} = Q^{(k_0+1)}` is finite. Every `q ∈ Q^∞` is a level-1 section of some
element of `Q^∞`. Following predecessors inside the finite set `Q^∞` eventually repeats, so:
- `q = q''|_{v'}`, where `q''|_v = q''` for some nonempty `v`;
- `q'' ∈ K` acts trivially, so `v^{q''} = v` and `q'' ∈ Fix_v ∩ K`;
- `q'' ≠ 1` (otherwise `q = 1`), so `v = c^n` and `q'' ∈ C_c ∩ K`.

## 3. Kills

Assume every component has rank at most `1`. Then `C_c = p_c^{-1} ⟨w⟩ p_c` for the cycle
word `w` of the component of `c`, or `C_c = 1` for a tree component. Suppose `G` is finitely
presented, and let `q = q''|_{v'}` be as in §2.
- Write `q'' = p^{-1} w^j p` with `w^j ∈ K`, so `o = ord(w)` divides `j`.
- If `w` has infinite order, or `C_c = 1`, then `q'' = 1`, which is excluded.
- Otherwise the two identities give `q = h^{-1} ((w^o)|_y)^{j/o} h` for some word `h` and
  vertex `y`. Since `(w^o)|_y ∈ Q_E`, we get `q ∈ ⟨⟨Q_E⟩⟩`.

So `⟨⟨Q^∞⟩⟩ ⊆ ⟨⟨Q_E⟩⟩ ⊆ K`.

- **(a)** If there are no finite-order cycle words, then `Q^∞ = ∅`. By item 1 of
  `pure-loop-self-replicating-groups-are-not-fp`, `T_k(K) ⊆ ⟨⟨∅⟩⟩ = 1` for large `k`.
  Then `τ : G → F` is injective, since `ρτ = id`. So `G` is free, but `G ⊇ M_11` has
  torsion. Contradiction.
- **(b)** If `G` is finitely presented, then `T_k(K) ⊆ ⟨⟨Q^∞⟩⟩ ⊆ ⟨⟨Q_E⟩⟩` by the same
  item 1. Conversely, `Q_E` is finite, section-closed and contained in `K`, so
  `T_k(K) ⊆ ⟨⟨Q_E⟩⟩` makes `G` finitely presented by the same item 1.
- **(c)** Suppose `G` is finitely presented. By (b), `τ` embeds `G` in
  `Γ_E = F/⟨⟨Q_E⟩⟩ = *_i Γ_i`, where `Γ_i = F(S_i)/⟨⟨Q_i⟩⟩` and `Q_i` is the set of chosen
  conjugates lying in `F(S_i)`.
  - `G` is one-ended (`pure-loop-self-replicating-groups-are-not-fp`, item 2), so it is
    freely indecomposable and not `ℤ`.
  - By the Kurosh subgroup theorem, `τ(G) ≤ g Γ_i g^{-1}` for some `i` and `g`.
  - Applying `ρ` gives `G ≤ ρ(g) ρ(F(S_i)) ρ(g)^{-1}`. So `ρ(F(S_i)) = G`, contradicting
    properness.

## 4. Proper images

The first three cases are immediate:
- `G` is not cyclic, since it contains `M_11`;
- `G` is infinite, while the rooted letters generate the finite group `M_11`;
- `G → P` is onto, so a proper root image gives a proper subgroup.

For the fourth case, bounded automorphisms (those with a uniformly bounded number of
nontrivial sections per level) form a group (Sidki).
- `L` is section-closed, so every section of every word over `L` is again a word over `L`.
- A state letter `s ∈ L` has a nontrivial level-`n` section only at the loop vertex
  `(x_s, r_s^{n−1})` and, for `n = 1`, at finitely many rooted sections. So `⟨L⟩` is
  bounded.

Now let `s` be the unbounded witness, with `s|_{x'} = a' t^{±1} b'` for some `x' ≠ x_s`, and
`t` non-rooted.
- `ℓ_t ≠ 1`. Otherwise `t = C^{-1}D^{-1}` would be rooted, but `t` has a section with
  nontrivial root.
- `ℓ_t|_{r_t} = ℓ_t` (§2), so `t` and `t^{-1}` have nontrivial sections at every level.
- Put `b' = x'^{π_A^{-1}}`, so `ℓ_s|_{b'} = s|_{x'}`. Note `b' ≠ r_s`, since
  `ℓ_s|_{r_s} = ℓ_s` has state letter `s`, not `t`.
- For `0 ≤ j < n`, the vertex `(x_s, r_s^{j−1}, b', …)` (for `j = 0`, the vertex `(x', …)`)
  carries a nontrivial section. Here the tail follows the loop of `t^{±1}`.
- These `n` vertices are distinct. Vertex `j` has `b'` (or `x'`) in position `j + 1`, while
  every `j' > j` has `r_s` (or `x_s`) there.

So `s ∉ ⟨L⟩`, and `⟨L⟩ ≠ G`.

## 5. Same-point dichotomy and the bounded kill

- **Dichotomy.** With two state letters, `Γ_1` has two edges. A component of rank `2` has
  two edges and one vertex, so it is a bouquet `r_s = w_s = r_t = w_t = z`.
- **Bouquet.** `π_{ℓ_s} = π_A π_s π_B` maps `r_s ↦ w_s`, so it fixes `z`, and
  `ℓ_s|_z = s|_{z^{π_A}} = s|_{x_s} = ℓ_s`. The same holds for `t`. So in the basis
  `{a, e, ℓ_s, ℓ_t}` the state root image lies in `Stab(z)`, and (A') holds. Both letters
  loop at `z`, so (C'') fails.
- **Ray-loop subgroup.** Each of `ℓ_s` and `ℓ_t` is its own eventual section along `z^∞`,
  so both lie in the ray-loop subgroup of `fp-self-similar-groups-have-fp-ray-loop-subgroups`
  at `z^∞` (its item 3, with the letter `1` renamed `z`).
- **Bounded kill.** If every state letter is bounded, then `G` is generated by a bounded
  automaton, hence contracting (Bondarenko–Nekrashevych). By Lemma S, `G = G^X ⋊ P`, so `G`
  is regular branch over itself. It is therefore not finitely presented (Bartholdi, as
  cited in `fully-self-replicating-tree-groups-give-fg-tits-hosts`).

**Lemma S (the family is fully self-replicating).** Let `ρ_s` be the rooted word for `π_s`,
and `h = s ρ_s^{-1} = (ℓ_s, α, β, [t], 1, …)`. Then `h` has trivial root and support
`{0, 1, 2, (3)}`.
1. `M_11` is 4-transitive, so there is `m` mapping `(2, 0, 1, 3)` to `(1, p, q, r)` with
   `p, q, r ∉ {0, 1, 2, 3}`.
2. `h^m` carries `β` at `1`, and its other support points lie outside `{0, 1, 2, 3}`. So
   `[h, h^m] = [α, β]@1`.
3. Conjugating by `h` acts on the coordinate `1` by `α`. Conjugating by `h^{m'}`, with
   `2^{m'} = 1`, acts on it by `β`. `M_11` is simple, so `M_11@1 ⊆ G`.
4. Rooted conjugation then gives `M_11@x` for every `x`.
5. `t ρ_t^{-1} (α@4)^{-1} = ℓ_t@0` gives `t@0`, and then `t@x` for every `x`.
6. `h (α@1)^{-1} (β@2)^{-1} (t@3)^{-1} = ℓ_s@0` gives `s@x` for every `x`.

So `G@x ⊆ G` for all `x`. Every generator lies in `G^X ⋊ P`, hence `G = G^X ⋊ P`.

## 6. The screen (item 6)

`same_point_screen.py` decides the following for each recursion:
- (U) and (L1), by DFS on the weight-preserving digraph;
- `Γ_1`, its components and cycle words (`loopgraph.components`), with `Δ_2` compared
  against `Γ_1`;
- boundedness;
- orders of the cycle words;
- `Q_E` (`Rec.closure`, exact);
- the Kurosh blocks.

**Orders.**
- An infinite order is certified by a strongly connected component of the power-section
  graph `u → canon((u^ℓ)|_x)` that contains an edge of weight `ℓ > 1`. Since
  `ord(u) = lcm_x ℓ_x · ord((u^{ℓ_x})|_x)`, going once around such a cycle would give
  `ord(u) ≥ 2 ord(u)`.
- A finite order `o` is certified by `Rec.trivial(w^o)`, and by `w^{o/p}` being nontrivial
  for each prime `p | o`. `Rec.trivial` is an exact finite section-closure test.
- Every cycle word in the family received one of these certificates.

**Kurosh blocks.** The basis is the Nielsen basis of §2, with each cycle word containing a
state letter once substituted as a new letter. Letters that co-occur in a cyclically reduced
word of `Q_E` are merged. Each block is tested with item 4. The fourth case of item 4 uses
the section closure of the original letters in the block, and the witness `s` (with `s|_3 = t`).

The output is `same_point_screen.out`, and its tallies are the table of the claim.
