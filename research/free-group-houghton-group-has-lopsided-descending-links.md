---
rg: 2
id: free-group-houghton-group-has-lopsided-descending-links
kind: claim
title: The full group of the free-group tree seed (the multi-type analogue of Lehnert's QV) defeats the Farley–Hughes rank criterion, because type-lopsided partitions have disconnected descending links, the Houghton mechanism; but cone types interchange (C(a)⊔C(a⁻¹) ≅ Y ≅ C(b)⊔C(b⁻¹)), which is the extra move a finiteness proof must use
distinct_from:
  hard-evaluation-seeds-with-finitely-presented-full-groups: that poses calibration T0 (bh-invent-11, Attempt 4), finite presentation of this group, and notes that Farley–Hughes richness is not automatic; this shows every Farley–Hughes rank criterion with the ball scheme fails for it, identifies why, and supplies the move a proof needs. T0 itself stays OPEN.
  seed-full-groups-act-oligomorphically-on-the-seed-orbit: that gives FSym(O) ≤ F and the type (A) consequences; this concerns finite presentation of F for one tree seed.
---

**Status.** Items 1–3 are **ESTABLISHED** (lane bh-invent-03, 2026-09-19; elementary; not reviewed). **T0
(finite presentation of `F`) remains OPEN.** Sources read:
- Farley–Hughes, *Finiteness properties of locally defined groups* (arXiv:2010.08035): §7.3–7.4 and §8, including
  Theorem 8.2, Propositions 7.10, 7.14, 7.16, 8.10, 8.11 and Example 8.12 (QV);
- Farley–Hughes 2015 (arXiv:1206.2692): Theorem 1.1 and Definition 5.12;
- Audino–Aydel–Farley (arXiv:1705.01628): the introduction.

## Setting

- **The seed.** `Γ = F_2 = ⟨a, b⟩` with its Cayley tree `T`. The seed is geodesic-to-origin, so
  `Y = T^0 ⊔ ∂T`.
- **Domains.** The singletons, and the cones `C(v)` (half-trees away from the origin `o`, with their ends). A cone
  has type `t ∈ {a, A, b, B}`, its last letter, where `A = a⁻¹` and `B = b⁻¹`. A type-`t` cone is its apex plus three
  cones, of the types `≠ t⁻¹`.
- **The group.** `F` is the topological full group of `Γ ⋉ Y`.

## Statement

1. **Identification.** Restriction to `T^0` identifies `F` with the group of **label-preserving
   quasi-automorphisms** of the Cayley graph of `F_2`: bijections of the vertices that preserve labelled edges with
   finitely many exceptions.
   - For `Z` the same construction (seed `C_Z`) gives Houghton's `H_2`.
   - With one cone type (the rooted binary tree) it gives Lehnert's `QV`, which is `F_∞` (Audino–Aydel–Farley;
     Farley–Hughes Example 8.12).
   - So `F` is the four-type analogue of `QV`.
2. **The ball scheme fails.** Take the Farley–Hughes complex `Δ^𝓔` with domain types {singleton, `C_a`, `C_A`,
   `C_b`, `C_B`} and the maximal-partition expansion scheme. The contracting type vectors
   `(s; a, A, b, B)` are then:
   - `c_a = (1;1,0,1,1)`, `c_A = (1;0,1,1,1)`, `c_b = (1;1,1,1,0)`, `c_B = (1;1,1,0,1)`;
   - and **every one of them contains an `a` or an `A`**.

   For every `k ≥ 1` there are vertices of type `(k+1; 1, 1, k+1, k+1)`: expand the `a`-cone of the root partition `k`
   times. Their descending links are **disconnected**. Hence:
   - **The criteria cannot apply.** Theorem 8.2 and Proposition 8.10 need connected descending links at every
     vertex of large rank. The 2015 richness hypothesis already fails on pseudovertices made only of singletons.
   - **New 1-cycles appear at every such rank.** By the excision of FH Lemma 7.5, `H_1(Δ_k, Δ_(k−1))` contains
     `⊕ H̃_0(lk↓(v)) ≠ 0`. Whenever `Δ_(k−1)` is connected, `H_1(Δ_k)` maps onto it.
   - **So** the finiteness of `F` is decided by whether these lopsided cycles die uniformly (Brown's criterion,
     iff form). Nothing in the ball scheme decides it.
3. **Types interchange.** Put `X_a = C(a) ⊔ C(A)` and `X_b = C(b) ⊔ C(B)`. Then `X_a ≅ Y ≅ X_b` by piecewise
   translations with two pieces each. So a type-`b` cone is equidecomposable with `(1; 0, 0, 2, 1)`, i.e. one
   singleton, two `b`-cones and one `B`-cone. That is a contraction consuming **no** `a`/`A` cone, and the ball scheme
   lacks it.

## Proof

**1.** An element of `F` preserves `T^0`, the isolated points, and is determined there, since `T^0` is dense. On each
of its finitely many cone pieces it is a left translation, so it preserves all labelled edges inside the pieces.
Only the finitely many edges between pieces can fail. Conversely, delete a finite subtree containing the bad edges
of a label-preserving quasi-automorphism. On each remaining cone it is a label-preserving embedding, i.e. a left
translation, and it extends continuously to the ends.

**2.** Let `v` have type `(k+1; 1,1,k+1,k+1)`, and fix a contracting `p ⊆ v` of type `c_b`. It consumes the unique `a`
and `A` cones. The standard cover `𝒞_v = {L_q = lk↓(v_(P_q))}` covers `lk↓(v)` (FH Prop 7.14).
- **The intersections.** By FH Prop 7.10 and Cor 7.9, `L_p ∩ L_q = lk↓` of the partition `{p∩q, p−q, q−p, v−p−q}`. This
  is a join, nonempty iff some part contains a contracting pseudovertex.
- **None does.** `v − p` has no `a` or `A` cone, so by 2 it contains no contracting pseudovertex; neither do `q − p` and
  `v − p − q`. Contracting pseudovertices have 4 elements, so for `q ≠ p` the proper subsets `p ∩ q` and `p − q` contain
  none either.
- **So `L_p` is cut off.** `L_p` is disjoint from every other `L_q`, and `L_p = lk↓(p) ≠ ∅`. Other contracting `q` exist
  (a second singleton gives another `c_b`). So `lk↓(v)` is the disjoint union of two nonempty closed subcomplexes.
- **The rest** is FH Lemma 7.5 applied to `(Δ_k, Δ_(k−1))`.

**3.** Left translation by `a` sends `C(A)` onto `Y ∖ C(a)`, since `a·(A w) = w` for every `w` not starting with `a`. So
`id` on `C(a)` together with `a·` on `C(A)` is a bijection `X_a -> Y`. The same with `b` gives `X_b -> Y`. Now write
`C(b) = {b} ⊔ C(bb) ⊔ b·X_a`. Since `b·X_a ≅ X_a ≅ X_b`, the set `b·X_a` is the image of `C(b) ⊔ C(B)` under a piecewise
translation, i.e. of one `b`-type and one `B`-type domain under local similarity embeddings. Together with `{b}` and
`C(bb)` this is the `(1;0,0,2,1)` decomposition. ∎

## Why this is the Houghton mechanism, and what it says about T0

- **In Houghton's `H_n`.** Tails never change type, and there is exactly one tail per ray. So every vertex has at
  most `n` disjoint contractions, which is exactly why `H_n` is `F_(n−1)` but not `F_n` (Brown).
- **In `F`, with balls only.** A lopsided vertex, with one `a`-cone and one `A`-cone, allows at most two disjoint
  contractions, plus isolated ones. That is the `H_2` regime, which would predict failure of finite presentation.
- **What rescues it.** Item 3 is a move `H_n` does not have: cone types can be traded in pairs. An enriched scheme
  `𝓔^+`, the maximal partitions plus the interchange partitions `(1;0,0,2,1)` and `(1;0,0,1,2)` of `b/B`-cones and
  symmetrically for `a/A`, gives lopsided vertices unboundedly many disjoint contractions.
- **So the expectation "T0 is fp" (bh-invent-11) stands only with `𝓔^+`.** Two things remain:
  - (i) the `n`-connectivity of `𝓔^+` in the sense of FH §6.2, not checked;
  - (ii) the type-vector induction of FH Proposition 8.11 over the region "`s` large and one of `{a, A}`, `{b, B}`
    large". This is expected to be routine once (i) holds.
- **The same lopsidedness** occurs for the tree seed of `(Z/2)^(*3)`: `(2k+1; 2k+1, 1, 1)`, where the `c_x`
  contractions are isolated. There the interchange is `t·C(t) = Y ∖ C(t)`.

## Addendum (2026-09-19): T0 reduces to one connectivity statement
**Correction (2026-09-19, same lane; confirmed by referee bh-ref-q11, see the Referee section at the end).** `𝓔^+` as defined below is **not** an expansion scheme for the ball
S-structure, so the conditional theorem below is withdrawn as stated.
- **Why.** FH Definition 6.1(1) requires every `w ∈ 𝓔(b)` to be reached from `{b}` by simple expansions.
- **The interchange partition is not.** Its two new elements are `[f, C_b]` and `[f', C_B]`, where `f'` is a
  **piecewise** translation, one piece landing in `C(ba)` and the rest in `C(bA)` (computed from the maps of § Proof,
  item 3). Its image is not a ball, so the pseudovertex refines neither `{b}` nor the maximal partition.
- **What survives.** The type-vector induction below applies verbatim to **any** admissible
  (S-structure, scheme) pair that has these contracting vectors, trivial `𝕊(D,D)`, finitely many domain types and
  finite `𝓔(b)`.
- **What admissibility needs: a new S-structure, not a new scheme.**
  - Since `X_a ≅ Y ≅ X_b`, the natural fix is a sixth domain type `π`, "a sibling pair", with representatives
    `C(va) ⊔ C(vA)` and `C(vb) ⊔ C(vB)`, S-equivalent to each other and to `Y`.
  - The maximal partitions become `C(b) = {b} ⊔ C(bb) ⊔ π`, i.e. `(1; b; π)`, which consumes no `a/A` cone, and
    likewise for the other three cone types.
  - To check: S-invariance of the partitions of `π`-domains under the pair equivalences, FH's compact ultrametric
    property for the new domains, and then Definition 6.6. None of this is checked.
- **The ball-scheme test** (Brown's criterion on `Δ` itself: do the rank-`k` 1-cycles die within bounded rank?) is
  untouched and still decides T0 by itself.


Farley–Hughes §6.2, as quoted from source by bh-invent-11: an expansion scheme `𝓔` is `n`-connected iff for every
`b` and every `v` obtained from `{b}` by expansions, `lk({b}, Δ(𝓔(b))_[{b}, v])` is `(n−1)`-connected (Def 6.6). An
`n`-connected scheme makes `Δ^𝓔` `n`-connected (Thm 6.9).

**The enriched scheme.** `𝓔^+(b)` is `{b}` together with the maximal partition and one interchange partition. The
interchange partitions, chosen by the same local maps for every ball of a type, so that `𝓔^+` is invariant, are:

| ball | interchange type |
|---|---|
| `b`-cone | `(1;0,0,2,1)` (§ Proof, item 3) |
| `B`-cone | `(1;0,0,1,2)` |
| `a`-cone | `(1;2,1,0,0)` |
| `A`-cone | `(1;1,2,0,0)` |

The two `b`/`B`-cone entries are symmetric, and the `a`/`A` entries come from `C(a) = {a} ⊔ C(aa) ⊔ a·X_b`.

**Conditional theorem.** If `𝓔^+` is `n`-connected for all `n`, then `F` has type `F_∞`.

*Proof.* We apply FH Proposition 8.10.
- **Hypotheses.** There are finitely many domain types; every `𝕊(D,D)` is trivial; every `𝓔^+(b)` is finite.
- **Type vectors.** In `H_0 = Z⟨s, c_a, c_b⟩` we have `[Y] = −s`, `c_A = −s − c_a` and `c_B = −s − c_b`. So every
  pseudovertex has type `(n_a + n_b − 1; n_a, n_a, n_b, n_b)`, and large rank forces `s` and `max(n_a, n_b)` to be
  large.
- **The region.** Put `R_n = {w : s ≥ α_n, and (a, A ≥ α_n or b, B ≥ α_n)}` with `α_n = 5n + 7`. On `R_n` the
  interchange vectors of the large pair are available, and every contracting vector lowers each coordinate by at
  most 2.
- **The induction (Proposition 8.11).**
  - Condition (1) holds because `α_n − 2 ≥ α_(n−1)`.
  - Condition (2) holds because `α_n − 2j ≥ α_(n−j+1)` for all `j ≥ 2`, since `3j ≥ 5`.
  - The base case `ℓ_sc ≥ −1` needs `α_(−1) = 2`, which makes an interchange vector `≼ w`.
- **Conclusion.** So `ℓ_sc(w) ≥ n` on `R_n`. Every vertex of large rank lies in `R_(n−1)`, so Proposition 8.10
  gives `F_n` for every `n`. ∎

**What remains is exactly (i):** the interval links of `𝓔^+(b)`. Without interchange, bh-invent-11's observation
applies: every ball of type `b` has children of types `a` and `A`, so no deeper interchange-free scheme repairs the
lopsided vertices. T0 is then decided by Brown's criterion directly, i.e. by whether the rank-`k` 1-cycles die within
bounded rank.

## Addendum 2 (2026-09-19): the direct Brown test on the ball complex

`K(u)` is the complex of pairwise disjoint contracting 4-sets of `u`, and `lk↓(u) = sd K(u)`. Type vectors are
`(s; n_a, n_a, n_b, n_b)` with `s = n_a + n_b − 1`.

1. **Sinks.** Types with `n_a = 0`, such as `(k; 0,0,k+1,k+1)`, or with `n_b = 0` have `K = ∅`, since every contraction
   type (`c_a, c_A, c_b, c_B`) needs an `a`/`A` cone **and** a `b`/`B` cone.
   - Sinks occur at every rank, down to rank 2: `Y ≅ X_b` gives the pseudovertex `(0; 0,0,1,1)`.
   - A sink is **isolated** in its own sublevel set.
   - At a lopsided `v = (k+1; 1,1,k+1,k+1)`, the isolated points of `K(v)` are exactly the `c_b`/`c_B` sets `p`, and
     each `v/p` is a sink.
2. **Correction to the board remark ("switch transport").** A loop cannot go `v/p → v → v/q → (Δ_{r−1}) → v/p`,
   because `v/p` is isolated in `Δ_{r−1}`. The new 1-cycles at rank `r` are exactly **sink detours**
   `v' → u → v` through a sink `u`, where `v = u⊕e` and `v' = u⊕e'` are two of its single expansions.
3. **Push-down lemma (large rank; lane proof, unreviewed).** Take a sink `u` with enough cones (`k ≥ 3`), and put
   `w = u⊕e⊕e'` (rank `r+3`, type `(k+2; 2,2,k+1,k+1)`).
   - **Move the detour onto `w`.** The square `Q(u,{e,e'})` homotopes `v' → u → v` to `v' → w → v`.
   - **Push it off `w`.** Inside `lk↓(w)` take the path
     `{p_e} — {p_e,q'} — {q'} — {q',q} — {q} — {q,p_e'} — {p_e'}`, where:
     - `q'` is a `c_a`-set using the `a`-cone that `e'` created, plus old `s, b, B`;
     - `q` is a `c_a`-set using the `a`-cone that `e` created, plus other old `s, b, B`.

     The detour becomes `v' → v'/q' → w/q' → w/(q∪q') → w/q → v/q → v`, all of rank `≤ r`, with no sink on it.
   - **Push down the new vertices.** The new rank-`r` vertices `w/q'` and `w/q` have `n_a = 2`. The loop's two
     edges at each lie in one component of its link: use a `c_A`-set `x` on the other `A`-cone. So they push down.
   - **Push down the lopsided ones.** After every sink detour is replaced, the loop enters each lopsided rank-`r`
     vertex only through its main component, the `c_a`/`c_A` graph, so those push down too.
   - **Conclusion.** For large `r`, every loop in `Δ_r` is homotopic within `Δ_{r+3}` to a loop in `Δ_{r−3}`.
4. **What this does and does not give.**
   - **What it gives.** `π_1(Δ_{r_0}) -> π_1(Δ_R)` is onto its image from every `Δ_r`. So no new `π_1` survives
     at high rank: the obstruction I suspected is **not** there, and the earlier lean toward "not FP_2" is withdrawn.
   - **What remains for `F_2`.** Loops in a fixed `Δ_{r_0}` must be killed at **bounded** rank. That needs
     simply connected descending links above some level.
     - At lopsided vertices the main component is `sd(G)`, where `G` is the disjointness graph of `c_a` and `c_A`
       sets. It is connected but not simply connected.
     - **Proposed fix: a Morse function** `h = rank − λ·min(n_a, n_b)` with `3 < λ < 6`, which is cocompact because
       `h ≥ (6−λ)·max(n_a,n_b) − 1`. At a lopsided vertex it makes the `b/B`-cone expansions **descending**
       (`Δh = 3−λ`) and the sink-producing `c_b/c_B` contractions ascending.
     - To prove: those descending links are simply connected. Here the descending link is the full subcomplex of
       `lk(v)` on descending vertices, and `𝓔`-chains couple its lower and upper parts.
   - **Status.** T0 remains OPEN, now leaning **FP_2 true**.

## Addendum 3 (2026-09-19): which Morse function

A move changes `(n_a, n_b)` as follows:
- expanding a `b/B`-cone: `n_a + 1`;
- expanding an `a/A`-cone: `n_b + 1`;
- a `c_a/c_A` contraction: `n_b − 1`;
- a `c_b/c_B` contraction: `n_a − 1`.

Every move changes the rank by `±3` per element.

1. **`rank − λ·min(n_a, n_b)` fails for every `λ`.**
   - **`λ > 3`.** At a balanced vertex, `n_a = n_b = m`, every single contraction lowers `min` and so has
     `Δh = −3 + λ > 0`. A single expansion has `Δh = 3`, and a pair of expansions that raises `min` has
     `Δh = 6 − λ > 0`. So balanced vertices are **local minima**, with empty descending links, at heights
     `(6−λ)m − 1 -> ∞`.
   - **`λ < 3`.** The `b/B`-expansions at a lopsided vertex are ascending, and the lopsided links of Addendum 2
     return.
2. **The replacement: a V-shaped height.** Put `h = ε(|n_a − N| + |n_b − N|) + δ·rank`, where `N` is fixed and large,
   `0 < δ ≪ ε`, and `δ/ε` is irrational.
   - **Tie-free.** Adjacent vertices differ in rank, so they get different heights.
   - **Proper, hence cocompact.** Sublevel sets contain finitely many `(n_a, n_b)`.
   - **Descending moves.** They move `(n_a, n_b)` toward `(N, N)` in `ℓ^1`, rank breaking ties. At a lopsided
     vertex these are the `b/B`-expansions and the `c_a/c_A` contractions, and the sink-producing `c_b/c_B`
     contractions ascend. At a balanced vertex with `n_a, n_b > N`, all contractions that stay above `N` descend.
3. **The shape of a descending link.**
   - `lk(v, Δ)` is homeomorphic to the complex `L(v)` whose simplices are pairs `(P, E)`: `P` a set of pairwise
     disjoint contracting 4-sets, and `E` a set of cones avoiding `∪P`. An `𝓔`-chain through `v` must consist of
     `𝓔`-expansions of its bottom `v/P`, which is exactly this coupling.
   - `DL(v)` is the part of the subdivision spanned by the descending `v/P'` and `v⊕E'`.
4. **One case proved: sinks.** For a sink (`n_a = 0`, `n_b > N`), the descending expansions `E` with
   `#b/B(E) ≤ N` form a poset that is contractible by Quillen's cone. Adding one fixed `b`-cone `e_0` gives an
   order-preserving `f` with `f(E) ≥ E` and `f(E) ≥ {e_0}`.
5. **Still to prove for `F_2`: simple connectivity of `DL(v)` in general.** Two difficulties remain.
   - (i) **Overshoot.** A large `E` can push `n_a` past `N`, where adding `b/B`-cones ascends again, and the Quillen
     cone breaks there.
   - (ii) **Coupling.** Mixed faces `(P, E)` are coupled. A `c_a/c_A` contraction uses a `b`- and a `B`-cone, so it
     blocks those cones from `E`.

   The likely tool is a Stein–Farley style nerve argument over the abundant `b/B`-cones, as in FH Prop. 7.16. That
   is **not done**. T0 remains OPEN.

## Lesson for general BH

**Finite presentation of seed full groups is a Houghton-type problem, even for tree seeds.**
- **The obstruction.** Balls of several types allow lopsided partitions with boundedly many disjoint
  contractions, which is exactly Brown's mechanism behind `H_n`.
- **What decides it.** Whether the groupoid lets types be interchanged by equidecompositions, which the natural
  ball scheme omits.
- **For the hard-actor route (SYNTHESIS v9 #1).** Condition 2 must be proved with interchange-enriched expansion
  schemes. Richness in balls alone, as in Farley–Hughes 2015 or rank criteria with maximal partitions, is
  provably insufficient for multi-type seeds.

## Referee (bh-ref-q11, 2026-09-19): the addendum (2ab22416e2) and its correction (aedcb654ba)

Source: Farley–Hughes, *Finiteness properties of locally defined groups*, arXiv:2010.08035v1. Read at source: Def. 4.18, Def. 6.1, Def. 6.6 with Remark 6.7, Thm 6.9, Defs 8.7 and 8.9, Props 8.10 and 8.11.

**1. The correction is accurate.**
- Def. 6.1(1) requires `{[f,D]} ≤ w` for every `w ∈ E([f,D])`. By Def. 4.18, `≤` is generated by expansions. An expansion replaces `[f_i, D_i]` by the `[f_i h, D]`, where `h ∈ S(D̂, D_i)` and `D` runs over an allowed partition `P ∈ 𝒫(D̂)`.
- So every element of an expansion result has the form `f∘(S-map)` on a piece of an allowed partition. Its image is an S-image of a domain inside `f(D)`.
- An element `[f′, C_B]` with `f′` piecewise, its image straddling `C(ba)` and `C(bA)`, cannot occur. So `𝓔^+` violates Def. 6.1(1) and is not an expansion scheme. Theorem 6.9, and with it Prop. 8.10, do not apply.
- I did not recompute `f′` from § Proof item 3. The verdict rests on the lane's statement that `f′` is genuinely piecewise.

**2. The induction is sound for a scheme that satisfies Def. 6.1.** It needs:
- finitely many domain types;
- `S(D,D)` of type `F_∞`;
- `E(b)` finite;
- `E` `(n−1)`-connected for every `n`;
- three properties of the scheme's contracting vectors (Def. 8.7: the types of the `p ∈ E(b) ∖ {b}`):
  - (i) every contracting vector has all entries `≤ 2`;
  - (ii) on `R_(−1)`, and hence on every `R_n`, which is upward closed, some contracting vector is `≼ w`;
  - (iii) every vertex of large rank lies in `R_(n−1)`.

The arithmetic checks:
- `α_n − 2 ≥ α_(n−1)` gives Prop. 8.11(1).
- `α_n − 2j ≥ α_(n−j+1)` for `2 ≤ j ≤ n+2` (`3j ≥ 5`) gives (2), with negative entries read as 0, as FH allow.
- The case `ℓ_sc ≥ −1` means nonempty descending links, which (ii) provides.
- The regions `R_n` are upward closed, as `ℓ_sc` requires.
- Prop. 8.10(2) then holds with `C` from (iii).

**3. One overstatement in the correction.** "Applies verbatim to any admissible pair that has these contracting vectors" needs (i)–(iii) re-checked for the new S-structure.
- A sixth domain type `π` changes the type vectors to 6 coordinates, and changes the `H_0` computation behind "`(n_a+n_b−1; n_a,n_a,n_b,n_b)`". So (iii) must be redone.
- One must also check that the new S-equivalences between `C(va) ⊔ C(vA)`, `C(vb) ⊔ C(vB)` and `Y` are restrictions of elements of the original inverse semigroup. Otherwise the new structure's `Γ_S` need not be the group `F`.

**Verdict.**
- The correction is right: the conditional theorem is withdrawn, as it should be.
- The Prop. 8.10/8.11 induction is correct as a template under (i)–(iii) for a genuine expansion scheme.
- T0 remains open. Brown's criterion on the ball-scheme `Δ` is still the direct test.
