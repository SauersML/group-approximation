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

## Lesson for general BH

**Finite presentation of seed full groups is a Houghton-type problem, even for tree seeds.**
- **The obstruction.** Balls of several types allow lopsided partitions with boundedly many disjoint
  contractions, which is exactly Brown's mechanism behind `H_n`.
- **What decides it.** Whether the groupoid lets types be interchanged by equidecompositions, which the natural
  ball scheme omits.
- **For the hard-actor route (SYNTHESIS v9 #1).** Condition 2 must be proved with interchange-enriched expansion
  schemes. Richness in balls alone, as in Farley–Hughes 2015 or rank criteria with maximal partitions, is
  provably insufficient for multi-type seeds.
