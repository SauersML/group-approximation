# Overfold merges as free folds of one subgroup: a no-drop lemma and the death of the retract route

Worker swarm-0917-w17-w17-fp-pull (reframer / compute scout), September 19, 2026.
Target: `fpbs-mal-overfold-merges-never-help`, statement (O): `deep_j(Q) = law_j(Q)`.
Scripts and outputs: `experiments/fpbs-overfold-free-fold-2026-09-17/`.

Status: the target stays OPEN. This note does five things:
- gives a `Q`-free form (F) of (O) on orbits where `L_j` and `L_{j+1}`
  agree (Section 2);
- proves a no-drop lemma for hits (Section 3);
- verifies (F) exactly for `j = 1, d ≤ 6` and `j = 2, d ≤ 4`, which gives
  (O) on such orbits in finite `L`-sets of every size (Sections 4 and 6);
- refutes the retract route (Section 5);
- records two sharper conjectures, (R) and (O'), with exact data.

## 0. Notation

- `L = F(a,b)`, `φ : a ↦ a, b ↦ b a b^{-2}`, `t_j = φ^j(b)`,
  `L_j = ⟨a, t_j⟩ = φ^j(L)`. Every `L_j` has rank 2 and the chain is
  malnormal. `C_j` is the Stallings core of `L_j` (1, 3, 8, 20 vertices for
  `j = 0..3`), and `ι : C_{j+1} → C_j` is the induced immersion.
- `rk` is rank and `r̄(H) = rk H − 1 = −χ(Γ_H)`.
- For subgroups `K ≤ K'`, `rk(K' : K)` is the relative rank: the least
  number of elements of `K'` that generate `K'` together with `K`.
- As in the w16 "relative-rank form" (target claim, Attempts), for a
  finite `L`-set `Q` with base point `p`: `S = Stab_L(p)`,
  `K = S ∩ L_{j+1}`, `K' = S ∩ L_j`. When `Q` is `L_{j+1}`-transitive of
  size `d`, `K` has index `d` in `L_{j+1}`, `K'` has index `d` in `L_j`,
  `law_j(Q) = rk(K' : K)`, and

  ```text
  deep_j(Q) = min{ k : g_1..g_k ∈ S, ⟨K, g_1..g_k⟩ ⊇ K' }.
  ```

## 1. The transport identity for law

Let `P = L_j / K'` as a set, and let `L` act on it by `a ↦ a`, `b ↦ t_j`
(through the isomorphism `φ^j : L → L_j`). Then `law_j(Q) = law_0(P)`,
where `law_0(P) = rk(Stab_L : Stab_{L_1})` computed on `P`. This is
immediate from `φ^j` carrying the pair `(L_j, L_{j+1})` to `(L, L_1)`.
`check_law0.py` checks it against the direct pullback computation.

Census of `law_0` over all transitive `L`-sets `P` of size `d`, split by
whether `L_1` stays transitive (`law_census.py`, `census_d6.txt`):

| d | law 1 | law 2 | law 3 | not L_1-transitive |
|---|---|---|---|---|
| 3 | 5 | 1 | 0 | 1 |
| 4 | 16 | 7 | 0 | 3 |
| 5 | 41 | 43 | 0 | 13 |
| 6 | 143 | 386 | 3 | 92 |

Law 3 first appears at `d = 6`, with three classes.

## 2. Free-fold form of (O) on L_{j+1}-transitive levels (proved)

**Seeds of a subgroup.** Let `K` have finite index `d` in `L_{j+1}`.
Its core `Γ_K` is the `d`-sheeted cover of `C_{j+1}` (finite covers of a
core graph are core graphs). A *seed* is a pair `(u, v)` of vertices of
`Γ_K`; its element is `g = γ_u γ_v^{-1}`, where `γ_x` is a path in `Γ_K`
from the base point to `x`. Identifying `u` with `v` and folding gives the
core of `⟨K, g⟩`. The seed elements are exactly the elements of
`D = L_{j+1} · {u_c u_{c'}^{-1} : c, c' ∈ V(C_{j+1})} · L_{j+1}`, the union
of w16's lawful and overfold double cosets: a lift of `h_1 u_c` and of
`h_2^{-1} u_{c'}` (`h_i ∈ L_{j+1}` read in the cover) gives a seed with
element `h_1 u_c u_{c'}^{-1} h_2`. The seed is lawful iff `ι c = ι c'`
(equivalently `g ∈ L_j`) for the labels `c, c'` of `u, v`.

**Statement (F).** Let `j ≥ 0`, let `K` have finite index `d` in
`L_{j+1}`, and let `g_1, …, g_k ∈ D` (equivalently, `J` is reached from
`Γ_K` by `k` successive seed identifications). Put `J = ⟨K, g_1, …, g_k⟩`.
Call `J` *realizable* if `J ∩ L_{j+1} = K`, and a *hit* if moreover
`K' := J ∩ L_j` has index exactly `d` in `L_j`. (For realizable `J`,
`K' ∩ L_{j+1} = K`, so the `L_{j+1}`-orbit of the coset `K'` in `L_j/K'`
has size `d`; hence `[L_j : K'] ≥ d`, with equality iff `L_{j+1}` is
transitive on `L_j/K'`.) Then (F) says: for every realizable hit,

```text
rk(K' : K) ≤ k.
```

**Local form of (O).** Let `Q` be any finite `L`-set and `O` an
`L_j`-orbit of `Q` that is a single `L_{j+1}`-orbit. Components of
`Γ_{j+1}(Q) = Q ×_R C_{j+1}` correspond to `L_{j+1}`-orbits and components
of `Γ_j(Q)` to `L_j`-orbits, so exactly one component `Γ_O` of
`Γ_{j+1}(Q)` lies over `O`. A same-fibre seed over `O` lies in `Γ_O`, and
folding never leaves a component. Write `deep(O)`, `law(O)` for the
least numbers of seeds (all, resp. lawful) in `Γ_O` whose closure contains
`ker(m)` on `Γ_O`. (O_loc) says `deep(O) = law(O)`.

**Proposition 1.** (O) for `j` implies (F) for `j` and every `d`; and (F)
for `(j, d)` implies (O_loc) for every such `O` of size `d`, in particular
(O) for every `L_{j+1}`-transitive `Q` of size `d`.

*Proof.*
- (O) ⇒ (O_loc). Seeds over `O` and seeds over `Q ∖ O` are disjoint and do
  not interact (Γ_O is a component, and its image `m(Γ_O)` is the whole
  component of `Γ_j(Q)` over `O`). So `deep_j(Q) = deep(O) + deep(rest)`
  and `law_j(Q) = law(O) + law(rest)`, with `deep(rest) ≤ law(rest)`.
  If `deep_j(Q) = law_j(Q)` then `deep(O) ≥ law(O)`.
- (O_loc) ⇒ (F). Let `J` be a realizable hit. Pick representatives
  `x_1, …, x_{d−1}` of the nontrivial cosets `K' x_i` of `K'` in `L_j`.
  No `x_i` lies in `J`, since `J ∩ L_j = K'`. `J` is finitely generated,
  so by M. Hall's theorem (free groups are LERF) there is a finite-index
  `S ⊇ J` with `x_i ∉ S` for all `i`. Then `S ∩ L_j` is a subgroup of
  `L_j` that contains `K'` and misses every nontrivial coset of `K'`, so
  `S ∩ L_j = K'` and hence `S ∩ L_{j+1} = K`. In `Q = L/S` with `p = S`,
  the orbit `O = p·L_j ≅ L_j/K'` has size `d` and is one `L_{j+1}`-orbit.
  `Γ_O` is the base component of `Q ×_R C_{j+1}`, a `d`-sheeted cover of
  `C_{j+1}` with `π_1 = K`, so `Γ_O = Γ_K`. Each `g_i ∈ S ∩ D` is the
  element of a seed of `Γ_K`, and that seed is same-fibre because
  `g_i ∈ S` (w16), and the closure
  of these seeds contains `ker(m)` on `Γ_O` because `⟨K, g⟩ = J ⊇ K'`
  (w16's criterion, whose proof is local to the component). So
  `deep(O) ≤ k`, and (O_loc) gives `rk(K' : K) = law(O) ≤ k`.
- (F) ⇒ (O_loc). Take `p ∈ O`, `S = Stab_L(p)`, `K = S ∩ L_{j+1}` (index
  `d`), `K' = S ∩ L_j` (index `d`). A minimum witness `g_1..g_k ∈ S` gives
  `J = ⟨K, g⟩ ⊆ S` with `g_i ∈ S ∩ D` and `J ⊇ K'`. Then
  `K ⊆ J ∩ L_{j+1} ⊆ S ∩ L_{j+1} = K` and `K' ⊆ J ∩ L_j ⊆ S ∩ L_j = K'`.
  So `J` is a realizable hit, and (F) gives
  `law(O) = rk(K' : K) ≤ k = deep(O)`. The reverse inequality is trivial. ∎

So (F) for all `d` is equivalent to (O) restricted to orbits `O` on which
`L_j` and `L_{j+1}` have the same orbit. It does not reach cross-orbit
seeds (several `L_{j+1}`-orbits inside one `L_j`-orbit), which w16 treats
separately.

**Why this helps.** (F) no longer mentions `Q`. The object is the core
graph `Γ_K` (a `d`-sheeted cover of `C_{j+1}`), and a seed is any pair of
vertices of `Γ_K`, folded freely. `J ∩ L_{j+1}` and `J ∩ L_j` are read off
the pullbacks `Γ_J ×_R C_{j+1}` and `Γ_J ×_R C_j` at the base point.
Realizability is a constraint that the earlier `Q`-based searches imposed
implicitly.

**Correction to our own first scan.** An earlier run (`single_seed.py`,
`ss_*.txt`) reported "overfold hits". All of them had
`[L_{j+1} : J ∩ L_{j+1}] = 1 < d`, so they are not realizable and say
nothing about (O). All later scripts (`bfs_free.py` and after) prune to
`J ∩ L_{j+1} = K`.

**Coverage.** Proposition 1 makes every finite check of (F) at `(j, d)`
universal in `Q`. Suppose every realizable hit at `(j, d)` reached by `k`
seeds has `rk(K' : K) ≤ k`, for all `k ≤ ℓ − 1`, where `ℓ` is the largest
law value at `d`. Then (O_loc) holds on every orbit `O` of size `d`, in
every finite `L`-set `Q` of any size, on which `L_j` and `L_{j+1}` have
the same orbit.
- The classes of `K` at `(j, d)` are the transitive `L`-sets of size `d`
  (via `φ^{j+1}`). So for `|Q| = d` this re-checks w16's census.
- What is new is `|Q| > d`: w16's census stops at `|Q| ≤ 6`.
- It does not cover cross-orbit levels (an `L_j`-orbit made of several
  `L_{j+1}`-orbits). Those are the case w16 left open for large `n`.

Structural content, also new: the lemma of Section 3, the single-seed rank
data behind (R), and the retract counterexample of Section 5.

## 3. No-drop lemma (proved): every hit needs a rank-dropping fold

For `J = ⟨K, g_1, …, g_k⟩` write `δ(J) = rk K + k − rk J ≥ 0`, the number
of rank drops in the folding. `δ = 0` means that no fold ever identified
two vertices that were already joined.

**Lemma 2.** Let `K` have index `d < ∞` in `L_{j+1}`, and let
`g_1, …, g_k ∈ L` be arbitrary (not only seed elements). Suppose
`J = ⟨K, g_1, …, g_k⟩` satisfies `J ∩ L_j = K'` with `[L_j : K'] = d`.
Then `δ(J) ≥ 1`.

*Proof.* Suppose `δ(J) = 0`.
1. By Schreier's formula, `rk K = rk K' = d + 1`, since `K` and `K'` have
   index `d` in the rank-2 groups `L_{j+1}` and `L_j`.
2. The map `K * F(x_1..x_k) → J`, `x_i ↦ g_i`, is onto, and both sides are
   free of rank `rk K + k = rk J`. Free groups of finite rank are Hopfian,
   so the map is an isomorphism: `J = K * ⟨g_1, …, g_k⟩` freely.
3. `K ⊆ K' ⊆ J`, so also `J = ⟨K', g_1, …, g_k⟩`, and
   `K' * F(x_1..x_k) → J` is onto with source rank `rk K' + k = rk J`.
   So `J = K' * ⟨g_1, …, g_k⟩` freely as well.
4. Let `N` be the normal closure of `g_1, …, g_k` in `J`, and let
   `π : J → J/N`. By step 2, `π|_K` is an isomorphism. By step 3,
   `π|_{K'}` is an isomorphism.
5. `π|_K = π|_{K'} ∘ (K ⊆ K')`. Since `π|_K` is onto and `π|_{K'}` is
   injective, the inclusion `K ⊆ K'` is onto, so `K = K'`.
6. But `K = K'` puts `K' ⊆ L_{j+1}`, which gives
   `[L_j : L_{j+1}] ≤ [L_j : K'] = d`. In fact `L_{j+1}` has infinite index
   in `L_j`: a nontrivial malnormal subgroup of finite index in a free group
   is the whole group, and `L_{j+1} ≠ L_j`. Contradiction. ∎

Remarks.
- The lemma is `Q`-free. It uses only `rk L_j = rk L_{j+1}` and
  `[L_j : L_{j+1}] = ∞`, so it holds for any such pair in a free group.
- For a hit, `J = ⟨K', g⟩`, so `ex(J) := rk J − rk K' ≤ k`. Because
  `rk K = rk K'`, `δ(J) = k − ex(J)`. Lemma 2 says `ex(J) ≤ k − 1`.
- The lemma does not bound `law`. With `δ = 1`, it still allows a hit
  whose `K'` has large relative rank. Conjecture (O') in Section 6 is the
  quantitative version.

## 4. Single seeds: exhaustive scans and conjecture (R)

**Exhaustive single-seed scan** (`all_single.py`, files `as_j*_d*.txt`).
For every class of `K` at `(j, d)` and every seed `(u, v)` of `Γ_K` with
distinct `C_{j+1}`-labels, the script:
- folds and tests realizability (`[L_{j+1} : J ∩ L_{j+1}] = d`);
- tests for a hit (`[L_j : J ∩ L_j] = d`);
- for a hit, computes `law(K')` through the transport identity.

Seeds with equal labels have `g ∈ L_{j+1} ∖ K` and are never realizable.

| j | d | classes | overfold realizable | overfold hits | lawful hits (all law 1) |
|---|---|---|---|---|---|
| 1 | 1 | 1 | 21 | 2 (`J = L`, law 1) | 7 |
| 1 | 2 | 3 | 248 | 0 | 42 |
| 1 | 3 | 7 | 1313 | 0 | 91 |
| 1 | 4 | 26 | 8700 | 0 | 294 |
| 1 | 5 | 97 | 50775 | 0 | 581 |
| 1 | 6 | 624 | 470760 | 0 | 1806 |
| 2 | 3 | 7 | 10932 | 0 | 208 |
| 2 | 4 | 26 | 72276 | 0 | 672 |

So, for `d ≥ 2`, **no realizable single overfold seed is ever a hit** in
this range. A lawful single-seed hit has `law ≤ 1` trivially.

Consequence. The law census (Section 1) gives `law ≤ 2` for `d ≤ 5`, and
the law of `K'` at level `j` is `law_0` of an `L`-set of size `d`. So
level `k = 1` is all that (F) needs there, and Proposition 1 gives:

> (O_loc) holds, for every finite `L`-set `Q` of any size, on every
> `L_j`-orbit of size `d` that is a single `L_{j+1}`-orbit, for
> `j = 1, d ≤ 5` and `j = 2, d ≤ 4`.

At `j = 1, d = 6`, the three law-3 classes need level 2 as well. Section 6
supplies it, which extends the statement to `j = 1, d ≤ 6`.

**Rank profile** (`single_stats.py`, files `stats_j*_d*.txt`). For every
realizable single overfold seed, the script records `r̄(J) − d` (1 for no
drop, 0 for one drop) and whether `J ∩ L_j` has finite index.

| j | d | realizable overfold seeds | r̄(J) − d = 1, J ∩ L_j infinite index | drops |
|---|---|---|---|---|
| 1 | 1 | 21 | 19 | 2, both hits with `J = L` |
| 1 | 2..5 | 248, 1313, 8700, 50775 | all | 0 |
| 2 | 1 | 174 | 168 | 6, all hits of index 1 |
| 2 | 2..4 | 2076, 10932, 72276 | all | 0 |
| 3 | 1 | 1138 | 1124 | 14, all hits of index 1 |
| 3 | 2 | 13628 | all | 0 |

**Conjecture (R).** For `d ≥ 2`, a realizable single overfold seed never
drops rank: `J = K * ⟨g⟩`.

By Lemma 2, (R) implies that no realizable single overfold seed is a hit
when `d ≥ 2`. At `d = 1` every hit has `K' = L_j` and law 1. So (R)
implies the level-1 case of (F) for all `(j, d)`: **`deep = 1` forces
`law = 1`**, on every coincident orbit of every finite `Q`. (R) is where
malnormality should enter. It is false at `d = 1`, where `K = L_{j+1}`
itself: there the drops give rank-2 groups `J` with `J ∩ L_j = L_j`
(at `j = 1`, `J = L`).

Two routes to (R) that fail on the data (`matching.py`, `rank_states.py`):
- *Matching.* The closure of a realizable overfold seed is not always the
  first-wave lift of its tree type with disjoint pairs. Classes of size 3
  occur: 170 of 1313 seeds at `j = 1, d = 3`, 844 of 8700 at `d = 4`, 194
  of 2076 at `j = 2, d = 2`. None of these drops rank. So (R) is not a
  purely local statement about the seed type.
- *SHNC equality.* SHNC for `J` against the rank-2 group `L_{j+1}` gives
  `r̄(J) ≥ r̄(J ∩ L_{j+1}) = d` for realizable `J`. So a drop means SHNC
  equality, with `J ∩ x L_{j+1} x^{-1}` of rank at most 1 for every other
  double coset. We hoped equality would force `J` to have finite index (a
  cover). It does not: lawful hits `J = K'` have `r̄ = d` and are not covers.

## 5. The retract route is dead (explicit counterexample)

**Route (G).** Every witness `J = ⟨K, g_1..g_k⟩ ⊇ K'` retracts onto `K'`.
A retraction `ρ : J → K'` would give (F) at once: `K' = ρ(J)` is generated
by `ρ(K) = K` and `ρ(g_1), …, ρ(g_k)`, so `rk(K' : K) ≤ k`. Weaker forms
would also suffice for a homological bound: `K'` a free factor of `J`, or
`H_1(K') → H_1(J)` split injective. The last is necessary for the others.

**Test** (`retract_test.py`, files `rt_j*_d*.txt`). The script runs the
exact realizable BFS to depth 2 over all classes of `K`. For every hit with
`J ⊄ L_j`, it computes the Smith normal form of `H_1(Γ_{K'}) → H_1(Γ_J)`
(`K'` read as the base component of `Γ_J ×_R C_j`) and `law(K')`. It
asserts the sanity case `J = K'` (split, `ex = 0`).

| j | d | hits with J ⊄ L_j (levels ≤ 2) | not split | of which minimal (law = level) |
|---|---|---|---|---|
| 1 | 2 | 5 | 1 | 0 |
| 1 | 3 | 19 | 3 | 1 |
| 2 | 1 | 12 (2 at level 1) | 0 | 0 |
| 2 | 2 | 138 | 3 | 0 |
| 1 | 4 | 169 | 13 | 0 |

The `j = 1, d = 4` run (`rt_j1_d4.txt`) finished. All 13 of its non-split
hits have law 1 at level 2. `rt_j2_d3.txt` was still going when this note
was written, so it is partial.

**The minimal counterexample** (`j = 1`, `d = 3`).
- `Q = Z/3` with `a` acting as `+1` and `b` as `−1`. Then `t_1 = b a b^{-2}`
  acts as `−1`, `L_1` is transitive, and `law_1(Q) = 2`.
- `S = Stab_L(0)` has rank 4. `K' = S ∩ L_1` and `K = S ∩ L_2` have index
  3 in `L_1` and `L_2`, and rank 4.
- The BFS finds `J = S` after two seeds (it collapses `Γ_2(Q)` onto the
  Schreier graph of `Q`). So `deep = law = 2`, and `S` is a minimum
  witness.
- `check_nonsplit.py` recomputes the map by Reidemeister–Schreier
  (transversal `a^i`), independently of the graph code. In Schreier bases
  the matrix of `H_1(K') → H_1(S)` is

  ```text
  [ 1 -1  0 -1 ]
  [-1  1  0 -1 ]
  [ 1  0  1  0 ]
  [-1 -1  0  1 ]      det = −4   (check_nonsplit.txt)
  ```

- `|det| = 4 ≠ 1`, so `H_1(K') → H_1(S)` is injective but not onto, and not
  split (the ranks are equal). So `K'` is neither a retract nor a free
  factor of the minimum witness `S`.

So (G) and its homological forms are false already at the minimum witness
of the first law-2 level. A proof of (O) cannot build a map `J → K'` that
fixes `K'`. Any argument must count generators without retracting, for
example through rank drops, as in Lemma 2 and (O').

## 6. Two seeds: exact data and conjecture (O')

**Conjecture (O').** For every realizable hit `J` reached by `k` seeds,

```text
law(K') = rk(K' : K)  ≤  δ(J) = k − (rk J − rk K').
```

(O') implies (F), because `δ ≤ k`. It also contains Lemma 2, because a
hit has `law ≥ 1`. It asks that each rank drop pays for at most one unit
of relative rank. In the example of Section 5, `δ = 2 = law`.

**Level-2 search on the high-law classes** (`level2.py`, files `l2_*.txt`).
The script takes every `L_1`-transitive `P` of size `d` with
`law_0(P) ≥ minlaw`, builds `K` at level `j` by transport, and runs the
exact realizable BFS to depth 2. No run hit the state cap. It records every
hit as (level, law of its `K'`).

| file | j | d | classes of K | hits (level, law): count | flags |
|---|---|---|---|---|---|
| `l2_j1_d4.txt` | 1 | 4 | 6 (law 2) | (1,1): 2, (2,2): 7 | 0 |
| `l2_j1_d6.txt` | 1 | 6 | 3 (law 3) | (2,2): 4 | 0 |

- In the law-3 run, no `K'` of law 3 is reached by two seeds. The hits at
  level 2 all reach other `K'` over the same `K`, of law 2.
- With the single-seed scan of Section 4, this finishes (F) at
  `j = 1, d = 6`. So **(O_loc) holds on every coincident `L_1`-orbit of
  size at most 6, in every finite `L`-set.**
- `l2_j2_d3.txt` (`j = 2`, `d = 3`): 1 class of `K` (law 2), hits
  (2,2): 1, 0 flags. This agrees with (F) at depth 2.

**(O') checks.** `retract_test.py` also tests (O') on every hit with
`J ⊄ L_j`, at depth 2 (`rt_*.txt`): 0 violations in the finished runs
(`j = 1, d = 2, 3, 4`; `j = 2, d = 1, 2`). Hits with `J = K'` satisfy (O') trivially (`δ = k` and
`law ≤ k`).

The rank profile at `j = 1, d = 3`, depth 2 (`rank_states_j1_d3.txt`)
shows what (O') is up against:
- level 1: lawful hits have `r̄(J) − d = 0`, that is `J = K'`; every
  realizable overfold state has `r̄(J) − d = 1` and misses;
- level 2: every hit has `r̄(J) − d ≤ 1` (`δ ≥ 1`), and 22 221 realizable
  states with `r̄(J) − d = 2` (`δ = 0`) never hit, as Lemma 2 requires.

## 7. Where this leaves (O)

Proved here:
- the `Q`-free form (F), with its equivalence to (O) on coincident orbits
  (Proposition 1, via M. Hall's theorem);
- Lemma 2: every hit has `δ ≥ 1`;
- the retract route (G), and its free-factor and split-`H_1` forms, are
  false at a minimum witness (Section 5).

Verified exactly and universally in `Q`, on coincident orbits:
- `j = 1`, orbit size `d ≤ 6`;
- `j = 2`, `d ≤ 4`.

Open, in order of reach:
1. **(R).** A realizable overfold single seed at `d ≥ 2` never drops rank.
   With Lemma 2 this gives the level-1 case of (F) for all `j, d`.
   Checked for `j = 1, d ≤ 5`; `j = 2, d ≤ 4`; `j = 3, d ≤ 2`.
2. **(O').** `law ≤ δ`. It implies (F), so (O) on coincident orbits.
3. **Cross-orbit levels.** `L_j`-orbits made of several `L_{j+1}`-orbits
   are outside (F) and need w16's Lemma A or a new idea.

A proof of (R) has to see `d`: (R) fails at `d = 1`, where rank drops do
produce hits (harmlessly, since law is 1 there). A proof of (O') cannot
go through a retraction (Section 5).
