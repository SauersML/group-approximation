---
rg: 2
id: hyperbolic-racgs-with-spread-nerves-contracting-rsg-proof
kind: route
title: Prove (NA) for hyperbolic RACGs from centralizers of reflections, realize every simplex as a state by the ray w_σ(rs)^∞, read off irreducibility from the nerve, and refine by cosets using an odd cycle
target: hyperbolic-racgs-with-spread-nerves-are-contracting-rsgs
requires:
  - greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
  - contracting-rsgs-closed-under-finite-index-overgroups
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-partials`, lane proof, not reviewed.

## The Davis cube complex (standard; recalled)

- `X` has vertex set `W`, an edge `{w, ws}` for each `s ∈ S`, and a cube `wW_T` for each simplex `T` of `L`. It is CAT(0)
  because `L` is flag.
- `W` acts by left multiplication: freely on vertices, with one vertex orbit, and cocompactly. The edge `{1,s}` is
  inverted by `s`.
- The hyperplane dual to `{w, ws}` is the wall of the reflection `wsw^{-1}`. Write `H_s` for the one dual to `{1,s}`.
- `H_t` separates `1` from `w` iff `t` is a left descent of `w`.
- **The order.** Label the edge `{w, ws}` at `w` by `s`, and fix a total order on `S`. This is `W`-equivariant.
- **Walls.** `Stab(H) = C_W(r_H)`, the centralizer of the reflection in `H`. Disjoint walls `H, K` have `r_Hr_K` of
  infinite order, and the walls `(r_Hr_K)^bH`, `b ∈ Z`, are pairwise distinct.
- **Reduced words (Tits).** A word is reduced iff no two equal letters are separated only by letters commuting with them.
  `t` is a left descent iff some occurrence of `t` is preceded only by letters that commute with `t` and differ from it.

## Step 1: (NA) holds

- Let `H, K` be disjoint walls with `Stab(H) ∩ Stab(K)` infinite.
- An infinite subgroup of a hyperbolic group contains an element `g` of infinite order, since torsion subgroups of
  hyperbolic groups are finite.
- `g` centralizes `r_H` and `r_K`, hence `z = r_Hr_K`. Centralizers of infinite-order elements of a hyperbolic group are
  virtually cyclic, so `g^a = z^b` with `a, b ≠ 0`.
- But `g^a ∈ Stab(H)`, while `z^bH ≠ H`. This is a contradiction.

## Step 2: finite radical, faithfulness and non-elementarity

- **No cone vertex.** By (a) applied to `σ = {s}`, no vertex is a cone point.
- **Irreducible.** If `L` were a join `L_1 ∗ L_2` with neither factor a simplex, two non-adjacent vertices in each factor
  would give an induced 4-cycle, against (H). So `W` is irreducible and not virtually cyclic, since `|S| ≥ 3`.
- **Faithful on `∂W`.**
  - Let `1 ≠ n` act trivially on `∂W`. Some conjugate of `n` lies in `W_T` for a simplex `T`, because finite subgroups
    are conjugate into spherical parabolics and every element of `W_T` is a product `w_{T'}` of distinct commuting
    generators.
  - The conjugate `w_{T'}` then also acts trivially. Pick `t ∈ T'` and `u ∉ St(t)`.
  - The ray `(ut)^k` crosses the walls of `⟨u,t⟩` beyond `H_u`. Each of them misses `H_t` and separates the ray further
    from `N(H_t)`, so its limit `ξ` lies in `Λ(H_t^-) ∖ Λ(H_t)`.
  - The ray `w_{T'}(ut)^k` lies in `H_t^+`, since `t` is a left descent there, and its limit is `w_{T'}ξ`.
  - So `w_{T'}ξ ≠ ξ`, a contradiction.
- So `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs` applies: (NA) holds and the action is free on vertices.

## Step 3: the states are exactly the nonempty simplices

- **States are simplices.** `S(1,ω)` is a set of pairwise crossing adjacent hyperplanes (quarter lemma), that is, a set
  of pairwise commuting generators: a simplex.
- **Every nonempty simplex is a state (uses (a)).** Given `σ ≠ ∅`, choose `r ∉ ⋃_{s∈σ} St(s)` and `s ∈ σ`. Let `ω_σ` be
  the Roller limit of the geodesic `v_k = w_σ(rs)^k`, where `w_σ` is the product of `σ`.
  - The word is reduced. The letters of `σ` commute with each other. Between the two occurrences of `s` stands `r`, which
    commutes with no element of `σ`. The letters `r` and `s` alternate.
  - Its left descents are exactly `σ`: every later letter is preceded by `r` or `s`, which it does not commute with.
  - So `S(1, ω_σ) = σ`.

## Step 4: the transitions

- **The rule.** By Step 1 of `greedy-cube-codings-rsg-proof`, with `e` labelled `s_0 = min σ`: at the vertex `s_0`, the
  edge labelled `t` crosses `H_{s_0}` iff `t ∈ lk(s_0)`, and the edge labelled `s_0` is `e^{-1}`. Translating back by
  `s_0` preserves labels. So `σ → τ` iff `s_0 ∉ τ` and `τ ∩ lk(s_0) = σ ∖ {s_0}`.
- **The greedy map.** `f(ω) = s_0ω` on the piece of `σ`.

## Step 5: irreducibility

- **Every state reaches a singleton.** `σ → σ ∖ {s_0}` whenever `|σ| ≥ 2`.
- **Singletons.** `{s} → {t}` iff `t ∉ St(s)`. So the singletons are strongly connected by (b).
- **Singletons reach everything.** `{r} → τ` iff `τ ∩ St(r) = ∅`. By (a), for every `τ` there is such an `r`.
- **Branching.** Suppose every singleton had a single successor. Then `𝒩` would be a perfect matching; being connected, a
  single edge; so `|S| = 2`, against (0). Hence the graph is strongly connected and not a cycle.
- **Conclusion.** By `sft-irreducible-core-iff-unique-recurrent-component`, the whole graph is an irreducible core, and
  (IRR) holds. With Step 2, item 1 follows from `greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs`.

## Step 6: finite-index subgroups and commensurable groups (no extra condition)

- **The refined graph.** Let `Γ ≤ W` have finite index. Its states are the pairs `(σ, c)` with `c ∈ Γ∖W`, and
  `(σ, c) → (τ, c·s_0)` whenever `σ → τ`.
- **The coding space.** Take `E` to be the paths starting at states with `c = Γ`. The coset coordinate is determined by
  the word, so `E ≅ ∂X`, `Γ`-equivariantly.
- **RSG.** If two words end in the same refined state then `Γu_w = Γu_{w'}`, so the canonical similarity `u_{w'}u_w^{-1}`
  lies in `Γ`.
- **Finite nucleus.** A local action of `h ∈ Γ` is `k = u_v^{-1}hu_w` from Lemma E, together with two cosets.
- **Loops at `{m}` generate `W`.**
  - The closed walks `m,k,m` and `m,k,l,k,m` along `𝒩` have labels `mk` and `mklk`, so `lk` is a loop label.
  - Inductively, `ab` is a loop label for every edge `a–b` of `𝒩`. Along paths in `𝒩` this gives every product `st`, so
    all of `W⁺` by (b).
  - **An odd loop exists (repair, 2026-09-19; the first version assumed (c)).** If `L` has an edge `{t,t'}`, (a) for
    `σ = {t,t'}` gives `s ∉ St(t) ∪ St(t')`, and `{s} → {t,t'} → {max(t,t')} → {s}` is a closed walk of
    length 3, with a label of odd length. If `L` has no edge, `𝒩` is complete on `≥ 3` vertices and has a triangle.
  - So the loops act transitively on `Γ∖W`, and the refined graph is strongly connected. It is not a cycle, since it
    covers a branching graph.
- **Conclusion.** `Γ` is a contracting RSG. A group commensurable with `W` contains such a `Γ` with finite index;
  apply `contracting-rsgs-closed-under-finite-index-overgroups`. ∎

## For the referee

- Step 1 uses only standard facts about hyperbolic groups.
- Step 2's faithfulness argument could be replaced by a citation: infinite irreducible Coxeter groups have trivial finite
  radical.
- The analytic input (Lemmas B, C, Z, E) is in `greedy-cube-codings-rsg-proof`.

## Referee (bh-ref-q11, 2026-09-19): PASS

The analytic input, `greedy-cube-codings-rsg-proof`, passes review (Referee section there; nits N1–N3 do not affect this node).

**Step 1 ((NA), the automatic disjointness of limit sets): correct.**
- Disjoint walls give `⟨r_H, r_K⟩ ≅ D_∞`. A finite dihedral group would fix a point of `X`, which would lie on both walls.
- `z^bH = H` would put `z^b` in `C(r_H)`. Then `z^{-b} = r_Hz^br_H = z^b`, so `b = 0`.
- The remaining steps are sound: torsion subgroups of hyperbolic groups are finite; centralizers of infinite-order elements are virtually cyclic; hence `g^a = z^b`.
- With quasiconvexity of wall stabilizers, this gives disjoint limit sets for disjoint walls, for every hyperbolic RACG.

**Step 2: correct.**
- **Faithfulness.** `w_{T′}(ut)^k` is reduced: `u ∉ T′`, since `u ∉ St(t)`, and `u` separates the two `t`'s. `t` is a left descent. The ray `(ut)^k` crosses only the pairwise disjoint walls of `⟨u,t⟩`, moving linearly away from `N(H_t)`, so `ξ ∉ Λ(H_t)`. Then `Λ(H_t^+) ∩ Λ(H_t^-) = Λ(H_t)` gives the contradiction.
- **Remark.** Irreducibility needs only (a). A join `L_1 ∗ L_2` has an edge `{a,b}` with `a ∈ L_1` and `b ∈ L_2`, and `St(a) ∪ St(b) = S`. So (H) is not needed there.

**Steps 3–5 (the nerve conditions): correct.**
- **Step 3.** `w_σ(rs)^k` is reduced with left descent set exactly `σ` (Tits). So `S(1, ω_σ) = σ`.
- **Step 4.** At the vertex `s_0`, the edge labelled `t` is dual to the wall of `s_0ts_0`. That wall crosses `H_{s_0}` iff `t ∈ lk(s_0)`, and it equals `H_t` then.
- **Step 5.**
  - `σ → σ∖{s_0}`.
  - `{s} → {t}` iff `t ∉ St(s)`.
  - `{r} → τ` iff `τ ∩ St(r) = ∅`, which (a) provides because `St` is symmetric.
  - Branching fails only if `𝒩` is a perfect matching, excluded by (b) and (0).

**Step 6: correct.** "Inductively" is valid, and here is the explicit form. Take a walk `m = w_0, …, w_q = a` in `𝒩` and an edge `a–b`. The loop out along the walk, across `a–b` and back, has label `x_b = β s_b β^{-1} s_m`. Here `β = s_{w_0}⋯s_{w_q}`, and the plain out-and-back loop has label `x_a = β s_a β^{-1} s_m`. So `x_a^{-1}x_b = g (s_a s_b) g^{-1}` with `g = s_{w_1}⋯s_{w_q}`.
- For even `q`, `g` is a product of walk-edge pairs `s_{w_{2i-1}} s_{w_{2i}}`.
- For odd `q`, `g = g′s_a` with `g′` such a product, and `s_a(s_as_b)s_a = s_bs_a`.

Induction on `q` gives `s_as_b ∈ G_loop` for every edge of `𝒩`, so `G_loop ⊇ W⁺` by (b).

**Dropping (c) (the 2026-09-19 repair): correct.**
- **The walk.** `{s} → {t,t′}` holds because `t, t′ ∉ St(s)`, by (a) and symmetry of `St`. `{t,t′} → {max}` drops the minimum. `{max} → {s}` holds because `s ∉ St(max)`.
- **Parity.** The walk has length 3 and odd label. Conjugating to the base singleton along an `𝒩`-path keeps the parity, so `G_loop` contains an odd element.
- **No edges.** If `L` has no edge, `𝒩` is complete on `≥ 3` vertices.
- **Conclusion.** `G_loop = W` from (0), (a) and (b) alone, and (c) is automatic.
- **The general form.** `contracting-rsgs-pass-to-finite-index-subgroups-via-loops`, with `contracting-rsg-coset-refinement-proof`, is also correct as read. It covers the cocycle labels `ℓ_β`, the lift `ψ`, the RSG step (`Γ′ℓ_β = Γ′ℓ_{β′}`), the nucleus in `Nuc_G × (Γ′∖G)²`, and the recurrent components as loop-group orbits.

**Instances: checked.**
- **`C_n`, `n ≥ 5`.** (H), (a), (b) and (c) all hold.
- **Dodecahedron and `L(n)`, `n ≥ 5`.** The nerve is the dual of the face structure, with no induced 4-cycle since there are no prismatic 4-circuits. Here (a) for all simplices is equivalent to the H³ node's (a), which is its vertex case. I rechecked all four vertex types of `L(n)` independently, and (b) and (c) (`T, d_1, d_3`); they match the H³ node.
- **Surface groups.** They are commensurable with the pentagon group, so this is a second route to `closed-surface-groups-are-contracting-rsgs`.

**Priority / credit.** I found no prior statement that hyperbolic RACGs, or 3-manifold groups, are contracting RSGs; the searches are recorded in `closed-surface-groups-contracting-rsg-via-bowen-series`, plus RACG-boundary and Kleinian searches on 2026-09-19. Credit:
- Davis, and Moussong for hyperbolicity;
- Tits for the word problem;
- Andreev, Pogorelov and Löbell for the polyhedra;
- Bowen–Series for the mechanism;
- BBMZ for the framework and the question.
