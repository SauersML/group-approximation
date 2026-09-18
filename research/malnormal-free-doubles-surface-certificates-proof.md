---
rg: 2
id: malnormal-free-doubles-surface-certificates-proof
kind: route
title: Cyclic cores give surface subgroups in doubles of free groups, and malnormal edge groups bound fatgraph segments
target: malnormal-free-doubles-surface-certificates
requires: [cyclic-graphs-of-free-groups-contain-surface-subgroups]
artifacts:
  - experiments/malnormal-doubles-surfaces-2026-09-17/stallings.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_genus1.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_cores.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/out_small.txt
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_fatgraphs.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/search_pairs.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/verify_lemma6.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/one_ended_certificate.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/one_ended_multi.py
  - experiments/malnormal-doubles-surfaces-2026-09-17/one_ended_primitive.py
---

Notation. `F = F(a,b)`. `C <= F` is finitely generated. `D(F,C) = F *_C Fbar` is the double:
`Fbar` is a second copy of `F`, and `c` is identified with `cbar` for `c` in `C`. `Gamma_H` is the
Stallings graph of `H <= F` with base vertex `*`. A word `w` is *filling* in a free group `A` if it
lies in no proper free factor of `A`.

## Lemma 1 (embedding)

Let `G = P *_C Q`. Suppose `P_0 <= P` and `Q_0 <= Q` satisfy `P_0 ∩ C = Q_0 ∩ C = E` (the same
subgroup of `C`). Then the natural map `P_0 *_E Q_0 -> G` is injective.

*Proof.* Take an element of `P_0 *_E Q_0` that is not in `E`. Write it as an alternating product
`g_1 ... g_k` with `k >= 1`, where each `g_i` lies in `P_0 \ E` or in `Q_0 \ E`, and consecutive
factors come from different sides.
- Since `P_0 ∩ C = E`, a factor `g_i` in `P_0 \ E` lies in `P \ C`. Likewise a factor in `Q_0 \ E`
  lies in `Q \ C`.
- By the normal form theorem for amalgams, such a product is not in `C` when `k >= 2`, so it is
  nontrivial. When `k = 1` it is not in `C` either.

Elements of `E` embed because `E <= C <= G`. So the kernel is trivial. ∎

## Lemma 2 (double of a cyclic core)

Let `A <= F` be finitely generated with `A ∩ C = <w>`. Let `Abar <= Fbar` be its copy. Then:
1. `<A, Abar> ≅ A *_<w> Abar` inside `D(F,C)`. The amalgam identifies `w` with `wbar` by the
   identity map.
2. **Surface case.** Suppose `A = pi_1(Y)` for a folded ribbon graph `Y` over `F` with one boundary
   component, genus `g >= 1` and boundary word `w`. Then `<A, Abar>` is the fundamental group of the
   closed orientable surface of genus `2g`.
3. **Wilton case.** Suppose `C` is malnormal in `F`, `rank A >= 2`, and `w` is filling in `A`. Then
   `A *_<w> Abar` is one-ended and hyperbolic, and contains a quasiconvex closed surface subgroup.
   Hence so does `D(F,C)`.

*Proof.*
- **(1).** `Abar ∩ Cbar` is the copy of `A ∩ C`, namely `<wbar>`. The identification `C = Cbar`
  sends it to `<w>`. Apply Lemma 1 with `E = <w>`.
- **(2).** Let `S` be the thickening of `Y`, a compact orientable surface of genus `g` with one
  boundary circle reading `w`.
  - The inclusion `pi_1(Y) -> F` is injective because `Y` is folded.
  - `A *_<w> Abar` is `pi_1` of `S ∪_∂ Sbar`, by van Kampen. This is the closed orientable surface
    of genus `2g`.
  - It embeds in `D(F,C)` by (1).
- **(3).** Two facts about `w` inside `A`:
  - **`<w>` is maximal cyclic in `A`.** Suppose `u` is in `A` and `u^k = w` with `k >= 2`. Then `u^k`
    lies in `C` and in `uCu^{-1}`, which contains `u^k`. So `C ∩ uCu^{-1} ≠ 1`, and malnormality
    gives `u ∈ C`. Hence `u ∈ A ∩ C = <w>`, a contradiction.
  - **`<w>` is malnormal in `A`.** Maximal cyclic subgroups of free groups are malnormal.

  Consequences:
  - `A *_<w> Abar` is hyperbolic by the Bestvina--Feighn combination theorem: amalgamation along a
    malnormal quasiconvex cyclic subgroup.
  - It is one-ended by Shenitzer's theorem: an amalgam of free groups over a cyclic group `<w>` is
    freely indecomposable iff `w` lies in no proper free factor on either side.
  - It is a graph of free groups with cyclic edge group. Wilton's theorem
    (`cyclic-graphs-of-free-groups-contain-surface-subgroups`) gives a quasiconvex surface subgroup.

  The closed surface lies in `D(F,C)` by (1). Hyperbolicity of `D(F,C)` itself is not needed to
  obtain the subgroup. ∎

**Conjugation.** `D(F, gCg^{-1}) ≅ D(F,C)`: apply `x -> g^{-1}xg` on `F` and `xbar -> gbar^{-1} xbar
gbar` on `Fbar`, which respects the identification. So Lemma 2 applies when `A ∩ gCg^{-1} = <w>`
for some `g`.

## Lemma 3 (finite check)

Let `c` be a vertex of `Gamma_C`, reached from `*` by a path labelled `g`. Then `A ∩ gCg^{-1}` equals
`pi_1` of the component of `(*, c)` in the fibre product `Gamma_A x Gamma_C`, based at `(*,c)`.

This is standard (Stallings). The rank of that component is `E - V + 1`, computed by
`product_component_rank` in `stallings.py`.

**Certificate.**
- In the surface case, `w = [x,y]` for a basis `x, y` of `A`. By Schützenberger's theorem `w` is not
  a proper power in `A`.
- So if `w` reads a closed path at `c` and the component has rank 1, the component group is `<u>`
  with `u^k = w`. Hence `k = 1`, and `A ∩ gCg^{-1} = <w>`.
- In the Wilton case `search_cores.py` uses only words `w` that are not proper powers in `F`.

## Lemma 4 (filling words cross every edge twice)

If `w` is filling in `A = pi_1(Gamma_A)` and `Gamma_A` is a core graph of rank `>= 2`, then the
closed path `w` crosses every edge of `Gamma_A` at least twice.

*Proof.* Let `e` be an edge.
- **`w` misses `e`.** Then `w` lies in `pi_1(Gamma_A - e)`, up to conjugacy.
  - If `e` separates, this is a free factor of a nontrivial free splitting. Both sides are
    nontrivial because `Gamma_A` is a core graph.
  - Otherwise it is a proper free factor of corank 1.
- **`w` crosses `e` exactly once.** Then `e` does not separate, since a closed path crosses a
  separating edge an even number of times.
  - Choose a maximal tree avoiding `e`. In the corresponding basis `{t} ∪ B`, where `t` is the
    element for `e`, cyclically `w = t u` with `u` a word in `B`.
  - `{tu} ∪ B` is a basis, so `w` is primitive and lies in the proper free factor `<w>`. ∎

## Lemma 5 (bounded segments)

Suppose:
- `C` is malnormal in `F`;
- `A ∩ gCg^{-1} = <w>` via the vertex `c` as in Lemma 3;
- `w` crosses every edge of `Gamma_A` at least twice;
- `w` is cyclically reduced and is not a proper power.

Let `K(C)` be the maximal length of a reduced path in the off-diagonal part of
`Gamma_C x Gamma_C` (the vertices `(p,q)` with `p ≠ q`). Then every unbranched segment of
`Gamma_A` (a path whose interior vertices have degree 2) has length at most `K(C)`.

*Proof.*
- **`K(C)` is finite.** `C` is malnormal iff every off-diagonal component of `Gamma_C x Gamma_C` is a
  tree. These components are finite, so reduced paths in them have bounded length.
- **The core is a circle crossed once.** Let `Z` be the component of `(*,c)` in `Gamma_A x Gamma_C`.
  It has rank 1, so its core is a circle. The closed path `w` at `(*,c)` is cyclically reduced, so it
  lies on the core circle and is a nonzero power of it. Since `w` is not a proper power, it runs once
  around the circle.
- **Distinct crossings sit on distinct circle edges.** Consequently, distinct crossings of `w` over
  the same edge of `Gamma_A` occur at distinct edges of the circle.
  - Two crossings of an edge `e: p -> q` in the same direction lift to circle edges starting at
    `(p, c_1)` and `(p, c_2)`. These are distinct, so `c_1 ≠ c_2`.
  - Two crossings in opposite directions give lifts `(p,c_1) -> (q,c_1')` and `(q,c_2) -> (p,c_2')`.
    If `c_1 = c_2'`, the lifts are the same product edge by determinism, crossed twice by a path that
    runs once around a circle. That is impossible, so `c_1 ≠ c_2'`.
- **Segments give off-diagonal paths.** Let `s` be a segment of `Gamma_A` with label `sigma`.
  - Every crossing of its first edge continues along all of `s`, because interior vertices have
    degree 2 and `w` is reduced.
  - Take two crossings of `s` and read them in the direction of `s`. They lift to two paths in
    `Gamma_C` reading `sigma`, starting from distinct vertices `c_1 ≠ c_2`.
  - Because `Gamma_C` is folded, the labels determine the paths in both directions. So the two
    paths never meet, and `(c_1,c_2)` reads `sigma` along a reduced off-diagonal path.
  - Hence `|sigma| <= K(C)`. ∎

**Corollary (exhaustive genus-1 search).**
- A genus-1 one-boundary folded ribbon graph is a rose `x y X Y` or a theta `x Y z X y Z`. In both,
  the boundary crosses each edge exactly twice.
- So in any genus-1 certificate for malnormal `C`, each edge word has length `<= K(C)`, and the
  finite enumeration in `search_genus1.py` with `L = K(C)` is complete.
- Its negative outputs `NONE` mean exactly this: *no folded genus-1 ribbon graph `Y` with boundary
  `w` has `pi_1(Y) ∩ gCg^{-1} = <w>` for any `g`*.

**Corollary (complete core enumeration along a fixed `w`).** By Lemma 4, a Wilton-case core along
`w` is a folded quotient of the circle graph of `w`.
- `A' <= A` implies `A' ∩ gCg^{-1} <= A ∩ gCg^{-1}`. So every admissible quotient is reached through
  admissible quotients by identifying one pair of vertices at a time.
- Hence `search_cores.py` lists every admissible quotient along `w`, up to its node cap, and says
  when a run was complete.
- An output `maxrank 1 complete True` means that no cyclic core of rank `>= 2` exists along `w`,
  whether filling or not.

## Lemma 6 (multi-boundary certificates)

Let `Y` be a folded ribbon graph over `F` of rank `r >= 2`, with boundary components `w_1, ..., w_k`.
Suppose that for each `j`:
- `w_j` is not a proper power in `F`;
- there is a vertex `c_j` of `Gamma_C` at which `w_j` reads a closed path, starting from the
  vertex `v_j` of `Y` where the boundary word begins;
- the component `Z_j` of `(v_j, c_j)` in `Y x Gamma_C` has rank 1.

Then `D(F,C)` contains the fundamental group of the closed orientable surface of genus `r`. That
surface is the double of the thickening `S(Y)` along all `k` boundary circles.

*Proof.* Let `A = pi_1(Y, *)` and let `p_j` be a path in `Y` from `*` to `v_j`. Let `q_j` be a path
in `Gamma_C` from the base vertex to `c_j`, and set `g_j = p_j q_j^{-1}` in `F`.

**Step 1: the two local conditions.**
- **(i) Edge stabilisers.** `A ∩ g_j C g_j^{-1}` is `pi_1(Z_j)` transported to the base (Lemma 3).
  It is cyclic and contains `u_j = p_j w_j p_j^{-1}`. By Lemma 3 its generator is a root of `u_j`,
  and `w_j` is not a proper power, so the group is `<u_j>`.
- **(ii) Distinct double cosets.** Components of `Y x Gamma_C` correspond to the double cosets
  `A g C`. The core circle of `Z_j` is the loop `w_j`.
  - A boundary word of a folded core ribbon graph is cyclically reduced: consecutive half-edges at a
    vertex carry distinct first letters. So the lift of `w_j` at `(v_j,c_j)` is a cyclically reduced
    closed path in the rank-1 graph `Z_j`, and it lies on the core circle. Since `w_j` is not a
    proper power, it runs once around that circle.
  - Suppose `Z_j = Z_l` with `j ≠ l`. Then `w_j` and `w_l` both run once around the same circle.
    Projecting to `Y`, they are the same cyclic path up to orientation, so the boundary circles
    `∂_j` and `∂_l` of `S(Y)` are freely homotopic in `S(Y)` up to orientation.
  - In a compact orientable surface with `chi < 0`, distinct boundary components are not freely
    homotopic, with either orientation. Here `chi(S(Y)) = 1 - r < 0`, a contradiction.
  - Hence the double cosets `A g_j C` are pairwise distinct.

**Step 2: the graph of groups.**
- Let `𝒢` have two vertices with groups `A` and `Abar`, and `k` edges `e_j` with groups `<w_j>`.
  The edge group embeds in `A` as `<u_j>` and in `Abar` as its mirror.
- `pi_1(𝒢)` is `pi_1` of `S(Y) ∪_∂ Sbar(Y)`, by van Kampen. This closed orientable surface has Euler
  characteristic `2 chi(Y) = 2(1-r)`, so genus `r`.

**Step 3: the morphism.** Define a morphism of graphs of groups from `𝒢` to the one-edge graph of
groups of `D(F,C)`:
- on vertex groups, the inclusions `A <= F` and `Abar <= Fbar`;
- on each edge `e_j`, the twisting elements `g_j` and `gbar_j`, which send `u_j` to the same element
  `c_j = g_j^{-1} u_j g_j` of `C`.

**Step 4: it is an immersion.** At the vertex `A`, the edges `e_j` go to the cosets `a g_j C`
(`a ∈ A`) of the Bass--Serre tree of `D(F,C)`.
- This map is injective on `⊔_j A/<u_j>` exactly when (i) and (ii) hold.
- The same holds at `Abar` by symmetry.

So the morphism is an immersion of graphs of groups. By Bass (*Covering theory for graphs of
groups*, JPAA 89 (1993), Prop. 2.7) it induces an injection on fundamental groups, via a locally
injective, hence injective, map of Bass--Serre trees. ∎

**Bounded segments with several boundaries.** The proof of Lemma 5 goes through when `C` is
malnormal and the hypotheses of Lemma 6 hold.
- Two crossings of an edge of `Y` lift to distinct vertices of `Y x Gamma_C` over the same vertex of
  `Y`:
  - if they lie in one `Z_j`, by the circle argument;
  - otherwise because they lie in different components.
- So their `Gamma_C`-coordinates differ, and the segment reads an off-diagonal path, of length at
  most `K(C)`.

Hence, for each rank `r`, `search_fatgraphs.py` with `L = K(C)` enumerates all certificates of
Lemma 6. It runs over:
- every connected multigraph with vertex degrees in `{3,4}` and rank `r`;
- every rotation system;
- every labelling by reduced words of length at most `K(C)`.

Its negatives are exact. Vertices of degree 2 are unbranched interior points of segments, and a
folded graph over `F_2` has degree at most 4.

## Lemma 7 (one-endedness certificate)

Let `S <= D(F,C)` be a closed orientable surface group of genus `>= 2` with `A <= S ∩ F` and
`Abar <= S ∩ Fbar`, as in Lemmas 2 and 6. Define subgroups `H_k <= F` by `H_0 = A` and

`H_{k+1} = < H_k, { u in F : H_k ∩ u H_k u^{-1} != 1 } >`.

If `H_k = F` for some `k`, then `D(F,C)` is one-ended.

*Proof.* `D(F,C)` is finitely generated and torsion-free, and it is not virtually cyclic because it
contains `S`. By Stallings' theorem it is enough to show that `D(F,C)` has no nontrivial free splitting.
Suppose `D(F,C)` acts on a tree `T` with trivial edge stabilisers and no global fixed vertex.
- **`S` fixes a unique vertex `v`.** `S` is freely indecomposable and not infinite cyclic, so by the
  Kurosh subgroup theorem it fixes a vertex. A nontrivial element fixes at most one vertex, because it
  would otherwise fix the edges of a geodesic between two fixed vertices.
- **Induction: `H_k <= Stab(v)`.** `H_0 = A <= S`. If `H_k <= Stab(v)` and `1 != h ∈ H_k ∩ u H_k u^{-1}`,
  then `h` fixes `v` and `u v`, so `u v = v`. Hence `H_{k+1} <= Stab(v)`.
- **Symmetry.** The involution of `D(F,C)` swapping `F` and `Fbar` (it fixes `C` pointwise) carries
  the same computation from `A` to `Abar <= S`. So `Hbar_k <= Stab(v)` as well.
- If `H_k = F`, then `F` and `Fbar` both fix `v`, so `D(F,C)` fixes `v`. This is a contradiction. ∎

`one_ended_certificate.py` computes `H_1, H_2, ...`, testing every reduced `u` of length `<= 4`. For
each accepted `u` it produces an explicit `h != 1` and checks by reading in the Stallings graph that
`h` and `u^{-1} h u` lie in `H_k`. It stops when `H_k = F` (one-ended) or when `H_k` stops growing
(undecided, which proves nothing).

## Lemma 7' (several certificates)

Let `A_1, ..., A_m <= F` be nontrivial subgroups. Suppose each `A_j` lies in a subgroup `S_j` of
`D(F,C)` that is freely indecomposable and not infinite cyclic. For example, `S_j` is the surface
subgroup `<A_j, Abar_j>` of a Lemma 6 certificate `Y_j` with `A_j = pi_1(Y_j)`. Define `H_0 = A_1`
and let `H_{k+1}` be generated by `H_k` together with
- every `u in F` with `H_k ∩ u H_k u^{-1} != 1`, and
- every conjugate `u A_j u^{-1}` (`u in F`) with `H_k ∩ u A_j u^{-1} != 1`.

If `H_k = F` for some `k`, then `D(F,C)` is one-ended.

*Proof.* As in Lemma 7, `D(F,C)` is finitely generated, torsion-free and not virtually cyclic. By
Stallings' theorem it is enough to rule out an action on a tree `T` with trivial edge stabilisers
and no global fixed vertex. Suppose such an action exists.
- **Fixed vertices.** A nontrivial element fixes at most one vertex of `T`. By the Kurosh subgroup
  theorem each `S_j` fixes a vertex `w_j`, so every nontrivial element of `A_j` fixes exactly the
  vertex `w_j`.
- **Induction: `H_k` fixes `v = w_1`.** This holds for `H_0 = A_1`. Suppose `H_k` fixes `v`.
  - If `1 != h ∈ H_k ∩ u H_k u^{-1}`, then `h` fixes `v` and `u v`, so `u v = v`.
  - If `1 != h ∈ H_k ∩ u A_j u^{-1}`, then `h` fixes `v`, and `u^{-1} h u`, a nontrivial element of
    `A_j`, fixes only `w_j`. So `h` fixes only `u w_j`, which gives `u w_j = v`. Hence
    `u A_j u^{-1}` fixes `u w_j = v`.

  So `H_{k+1}` fixes `v`.
- **The other factor.** Let `sigma` be the involution of `D(F,C)` that swaps `F` and `Fbar` and
  fixes `C` pointwise. The twisted action `g · x = sigma(g) x` again has trivial edge stabilisers
  and no global fixed vertex. The twisted action of `S_j` is the original action of `sigma(S_j)`,
  which is also freely indecomposable and not cyclic. So the argument above applies to the twisted
  action, and `F` fixes some vertex `v'` there. In other words, `Fbar` fixes `v'` in the original
  action.
- **Contradiction.** If `H_k = F`, then `F` fixes `v` and `Fbar` fixes `v'`. The group `C != 1` lies
  in both, so a nontrivial element of `C` fixes `v` and `v'`, which forces `v = v'`. Then
  `D(F,C) = <F, Fbar>` fixes `v`, a contradiction. ∎

`one_ended_multi.py` gathers every Lemma 6 certificate of a given rank for `C` from
`search_pairs.search(C, r, first_only=False)`. It rechecks each one with `verify_lemma6.verify`
before using it, and computes a basis of `A_j` from a spanning tree of `Y_j`. It then iterates the
two rules over all reduced `u` of length `<= 3`, including `u = 1`. Every witness `h != 1` is
checked by reading: `h` must close up at the base of `Gamma_{H_k}`, and `u^{-1} h u` must close up
at the base of `Gamma_{A_j}` (or of `Gamma_{H_k}`). The script stops at `H_k = F` (one-ended) or
when `H_k` stops growing (undecided, which proves nothing).

**Why several certificates help, and where they do not.**
- For `C = <AABa, aaba>` the search finds 16 rank-2 certificates. Their groups `A_j` all lie in
  the single rank-2 subgroup `<BA, baaa>`, so Lemma 7 stalls, and so does Lemma 7' restricted to
  rank 2.
- With the 144 certificates of ranks 2 and 3, Lemma 7' reaches `F` in one round
  (`out_one_ended_multi.txt`).

## Lemma 8 (one-relator certificate)

Suppose `C` has a basis `(y, c)` in which `y` is primitive in `F`. Let `phi, phi'` be automorphisms
of `F` with `phi(y) = phi'(y) = b`, and put

`r = phi(c)(a,b) · phi'(c)(e,b)^{-1}` in `F(a,b,e)`.

Suppose the Whitehead graph of the cyclic reduction of `r` is connected and has no cut vertex. Its
vertices are `a^{±1}, b^{±1}, e^{±1}`, and each cyclically consecutive pair `x x'` of `r` gives an
edge from `x` to `x'^{-1}`. Then `D(F,C)` is one-ended.

*Proof.*
- **Presentation.** `D(F,C) = (F * Fbar) / <<y ybar^{-1}, c cbar^{-1}>>`, since `y, c` generate `C`.
  The automorphism `phi * phi'bar` of `F * Fbar` carries this normal subgroup onto
  `<<b bbar^{-1}, phi(c) phi'(c)bar^{-1}>>`. Eliminating `bbar = b` by a Tietze move and writing `e`
  for `abar` gives `D(F,C) ≅ <a, b, e | r>`.
- **`r` is in no proper free factor.** By Whitehead's cut-vertex lemma, if a nontrivial cyclically
  reduced word lies in a proper free factor of a free group up to conjugacy, then its Whitehead
  graph for any basis is disconnected or has a cut vertex (J. H. C. Whitehead, *On certain sets of
  elements in a free group*, Proc. London Math. Soc. 41 (1936); J. R. Stallings, *Whitehead graphs
  on handlebodies*, in *Geometric group theory down under*, de Gruyter 1999). The hypothesis
  excludes both, and a conjugate of a free factor is a free factor.
- **`D(F,C)` is freely indecomposable.** By Shenitzer's theorem, a one-relator group `<X | r>` that
  is a nontrivial free product has `r` in a proper free factor of `F(X)` (A. Shenitzer,
  *Decomposition of a group with a single defining relation into a free product*, Proc. AMS 6
  (1955), 273--279).
- **Ends.** `D(F,C)` is finitely generated and torsion-free. It is not virtually cyclic, since `F`
  embeds. An HNN extension over the trivial group is a free product with `Z`. So Stallings' theorem
  gives one end. ∎

The three theorems are cited, not source-checked. Lemma 8 needs no surface certificate.

`one_ended_primitive.py` enumerates bases `(y, c)` of `C` by Nielsen moves up to depth 4. It tests
`y` for primitivity by greedy length reduction with the eight elementary Whitehead automorphisms of
`F_2`. A false negative here only loses a certificate; soundness rests on `check` below. It then builds `phi` with `phi(y) = b`, and composes each side
independently with `a -> b^i a^{±1} b^j`, `|i|, |j| <= 3`. It stops at the first `r` that passes the
graph test. A separate function `check` then re-verifies each certificate from the printed data:
- `<y, c>` and `C` have the same Stallings graph, by mutual membership;
- `phi(a), phi(b)` generate `F`, because their Stallings graph is the rose, and likewise for `phi'`;
- `phi(y) = phi'(y) = b`;
- `r` is recomputed, and the Whitehead graph test is rerun.

**Calibration.** The script certifies none of these freely decomposable doubles:
- `<a, bab^{-1}>`: the double is `<a, t | [a,t]> * <b>`, with `t = b^{-1} bbar`;
- `<a, b^2>`: the double is `<a> * <b, bbar | b^2 = bbar^2>`;
- `<aab, b> = F`: the double is `F`.

It certifies none of `<abAB, abaB>` either, whose double was not analysed. These runs used depth 2
and shift 1; the run at depth 4 and shift 3 did not finish in 600 s. With the same reduced
settings it still certifies `<AABa, aaba>`.

## Calibration

These are the outputs in `out_small.txt`:
- `C = F_2`: no certificate, as expected. The fibre product is `Gamma_A` itself, of rank 2.
- `C = <abAB>`: the rose `x = b, y = a` certifies. This recovers the genus-2 surface in the double
  along a commutator, a case covered by Wilton.
- `C = <aa,bb>` (not malnormal): no genus-1 certificate.
