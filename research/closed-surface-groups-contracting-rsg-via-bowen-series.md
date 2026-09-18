---
rg: 2
id: closed-surface-groups-contracting-rsg-via-bowen-series
kind: route
title: Code the circle by the Bowen–Series map of the right-angled (8g−4)-gon; itineraries are directed geodesic rays of tiles, the level of a cut point is the time its ray enters the wall's carrier, and fellow travelling makes the level defect match the Busemann shift, which gives a finite nucleus
target: closed-surface-groups-are-contracting-rsgs
requires:
  - contracting-rsgs-closed-under-finite-index-overgroups
  - sft-irreducible-core-iff-unique-recurrent-component
---

**Status.** All five steps are proved (lane `bh-partials`, lane proof, not reviewed). Steps 1–4 rest on sources read.
Step 5 is new here. Its delicate points are marked (★) for the referee.

## Sources read

**Katok–Ugarcovici**, arXiv:1610.00167v2 (Geom. Dedicata 191 (2017)), §1–§2:
- `Γ` is a closed genus-`g` surface group with Adler–Flatto's fundamental domain `F`: a regular `(8g−4)`-gon with all
  angles `π/2`, satisfying the Bowen–Series extension condition.
- Sides are paired by `σ(i) = 4g−i` (i odd) and `σ(i) = 2−i` (i even).
- `P_iQ_{i+1}` is the geodesic extending side `i`. It is the isometric circle of `T_i`.
- The points are in counterclockwise order `P_1, Q_1, …, P_{8g−4}, Q_{8g−4}`. Put `Π = {P_i, Q_i}`.
- **Prop. 2.2.** `T_i` maps `P_{i−1}, P_i, Q_i, P_{i+1}, Q_{i+1}, Q_{i+2}` to
  `P_{σ(i)+1}, Q_{σ(i)+1}, Q_{σ(i)+2}, P_{σ(i)−1}, P_{σ(i)}, Q_{σ(i)}`.
- **The map.** `f(x) = T_i x` on `[P_i, P_{i+1})`. It is Markov for `Π`, expanding, Rényi, and exact, with an invariant
  measure equivalent to Lebesgue.

**Bowen–Series**, Publ. IHÉS 50 (1979) 153–170 (NUMDAM scan, pp. 153–163 read), for a region `R` with property (*),
not a triangle:
- **Lemma 2.3.** `W = ⋃_i W(v_i)`, where `W(v_i)` is the set of endpoints of the arcs of the net through the vertex
  `v_i`. It satisfies `f(W) ⊆ W` and partitions `S¹`.
- **Lemma 2.4.** `f` and `Γ` are orbit equivalent, except for the pairs `(Q_i, g_{i−1}Q_i)`. That is, `x = gy` with
  `g ∈ Γ` iff `f^n x = f^m y` for some `n, m ≥ 0`.
- For the right-angled polygon, exactly two net geodesics pass through each vertex, both extending sides. So `W = Π`.

## Proof

**Step 1 (the SFT).**
- The states are the arcs `a_i = [P_i, Q_i)` and `b_i = [Q_i, P_{i+1})`.
- By Prop. 2.2: `T_i(a_i) = b_{σ(i)+1} ∪ a_{σ(i)+2}`, and `T_i(b_i) = b_{σ(i)+2} ∪ a_{σ(i)+3} ∪ ⋯ ∪ b_{σ(i)−2}`.
- **Cut points.** `B := ⋃_n f^{-n}Π`.
- **Group elements on cylinders.** `f^n` maps the cylinder `[w] = [s_0⋯s_n]` onto the arc `s_n` by `u_w^{-1} ∈ Γ`,
  where `u_w^{-1} = T_{i(s_{n−1})}⋯T_{i(s_0)}`.
- **The coding.** The itinerary map identifies `Σ_{Γ_BS}` with `S¹_B`, the circle Cantorized at `B` (cylinders are
  half-open arcs; `f` is expanding).

**Step 2 (RSG property).** For cylinders `[w]`, `[w']` with the same last state, `u_{w'}u_w^{-1} ∈ Γ` is the canonical
similarity `wω ↦ w'ω`.

**Step 3 (irreducible core).**
- Exactness gives mixing, and `μ` is equivalent to Lebesgue.
- So every state reaches every state in all large lengths, and `Γ_BS` is primitive.
- Its core is all of `Γ_BS` (`sft-irreducible-core-iff-unique-recurrent-component`).

**Step 4 (Γ acts on `S¹_B`, via Bowen–Series Lemma 2.4).**
- `B ⊆ Γ·Π` is clear.
- **The converse.** Let `x = gy` with `y ∈ Π`.
  - If `(x,y)` is not exceptional, Lemma 2.4 gives `f^n x = f^m y ∈ f^m(Π) ⊆ Π` (Lemma 2.3 with `W = Π`), so `x ∈ B`.
  - Exceptional pairs are `(Q_i, T_{i−1}Q_i) = (Q_i, P_{σ(i−1)})` (Prop. 2.2), and both points lie in `Π`.
- So `B = Γ·Π` is `Γ`-invariant, and `Γ` acts faithfully on `S¹_B` by homeomorphisms.

**Step 5 (finite nucleus).**

*Walls.*
- The tiling `Γ·F` is the chamber tiling of the right-angled Coxeter group of `F`. The neighbour across a side is forced
  to be the reflected polygon.
- So its **walls** (complete geodesics made of edges) are the Coxeter walls, and the tile distance (the word length for
  the side pairings) is the number of separating walls.
- Distinct walls are never asymptotic. They are lifts of closed geodesics of a torsion-free cocompact group; compare
  `horofunction-lemma-holds-for-free-and-surface-groups`.
- Every wall is `Γ`-equivalent to a side wall of `F`, so the set of wall endpoints is `Γ·Π = B`.
- Each point of `B` is an endpoint of exactly one wall.
- The **carrier** `car(W)` is the set of tiles with a side on `W`.

*Lemma A (itineraries are directed geodesic rays).*
- **Statement.** For `x ∈ S¹_B`, the tiles `τ_r(x) := u_r(x)F` form a geodesic ray from `F`. Every step crosses a wall
  that separates the current tile from `x`, and the ray converges to `x`.
- **Proof.**
  - `f^r x ∈ [P_i, P_{i+1}) ⊆ [P_i, Q_{i+1}]`, the arc enclosed by the isometric circle `C(s_i)`, while `F` lies
    outside it. So `u_r C(s_i)` separates `τ_r` from `x`, and `τ_{r+1} = u_r T_i^{-1}F` lies across it.
  - A crossed wall is never recrossed. Later walls separate later tiles from `x`, and the ray is already on `x`'s side.
  - So `r` distinct walls separate `F` from `τ_r`, and the ray is geodesic.
  - Far walls have small far-arcs, so the ray converges to `x`.
  - For `e ∈ B`, the one-sided points `e^±` use the one-sided branches. Before `f^r(e) ∈ Π`, the point `f^r e` is not
    an endpoint of any side wall, so the argument applies.

*Lemma B (level = carrier entry).* Let `e ∈ B` be an endpoint of the wall `W`, and put `lev(e) = min{r : f^r(e) ∈ Π}`.
- `lev(e)` is the least `r` such that `e` is an endpoint of a level-`r` cylinder.
- It is also the first time the ray `τ(e)` meets `car(W)`: `f^r e ∈ Π` iff `u_r^{-1}W` is a side wall of `F`, iff
  `τ_r ∈ car(W)`.

*Lemma C (directed rays enter carriers and stay).* Let `(τ_r)` be a geodesic ray whose every step crosses a wall
separating the current tile from `e`.
- **Heights.** Let `ht(τ)` count the walls disjoint from `W` that separate `τ` from `W`.
- **Carrier tiles have height 0.** A tile `τ ∉ car(W)`, on one side of `W`, lies in one column between consecutive
  rungs (walls perpendicular to `W`). The carrier tile `c` of that column is the column cut by the side walls of `c`
  not adjacent to its `W`-side. Those walls are disjoint from `W` (Bowen–Series Lemma 2.2: non-consecutive sides have
  disjoint circles). So some wall disjoint from `W` separates `τ` from `W`, and `ht(τ) ≥ 1` exactly off the carrier.
- **Height never increases.** The ray crosses only walls separating the current tile from `e`. A wall disjoint from `W`
  that has the current tile on `W`'s side also has `e` there, since `e ∈ ∂W` and the walls are non-asymptotic.
- **Height reaches 0.**
  - Every wall `V` counted by `ht(τ_r)` separates `τ_r` from `e`, so it is crossed later.
  - The ray converges to `e ∈ ∂W`. Being a quasi-geodesic in `H²`, it is eventually within a bounded distance of `W`,
    so infinitely many of its tiles are near `W`.
  - While `ht > 0` the ray keeps having walls to cross, and each crossing lowers `ht`. So `ht` reaches 0: the ray
    enters `car(W)`, and it stays there.
- **(★) Quantitative form.** If two such rays toward `e` are `c_1`-close from some time on, and one is in `car(W)` at
  time `t`, the other enters within `K_1` steps of the corresponding time.
  - The other ray then has `ht ≤ c_1`.
  - Each remaining wall `V` is disjoint from `W` and not asymptotic to it. So the region beyond `V` within distance
    `c_1 + 1` of `W` is compact.
  - By cocompactness its size is bounded uniformly over the finitely many configurations `(W, V)` up to `Γ`. The ray
    cannot stay beyond `V` longer than that.

*Lemma D (fellow travelling).* The tile graph is `δ`-hyperbolic. For `h ∈ Γ` and `ξ ∈ S¹`, the rays `τ(ξ)` from `F` and
`h·τ(h^{-1}ξ)` from `hF` satisfy `d(τ_{t+Δ}(ξ), hτ_t(h^{-1}ξ)) ≤ c_1` for all `t ≥ |h| + c`, with an integer shift
`|Δ(ξ)| ≤ |h|`. Here `c_1, c` depend on `δ` only, and `h` maps directed rays to directed rays. (★) If the rays to `ξ`
and `ξ'` from `F` share a prefix of length `≥ |h| + c'`, then `|Δ(ξ) − Δ(ξ')| ≤ c_2`.

*Lemma E (the local actions are bounded).* Fix `h`. Let `n = |w| ≥ n_0(h)`, let `[v]` be the smallest cylinder containing
`h[w]`, and let `k = u_v^{-1} h u_w`. Then `d(F, kF) ≤ K`, with `K` independent of `h`.
- **Lower bound, `|v| ≥ n + Δ − K_2`.**
  - Minimality puts a cut point `e` of level `|v|+1` in the interior of `h[w]`, so `h^{-1}e ∈ int[w]` has level `> n`.
  - By Lemma B, `lev(e)` and `lev(h^{-1}e)` are the carrier-entry times of the rays from `F` and from `hF` toward `e`.
  - **If `lev(e) ≥ |h| + c`,** Lemmas C(★) and D give `lev(h^{-1}e) ≤ lev(e) − Δ(e) + K_1`, so
    `n < |v| + 1 − Δ(e) + K_1`.
  - **If `lev(e) < |h| + c`,** the `hF`-ray enters by time `3|h| + c + K_1`, which contradicts `n ≥ n_0(h)`.
  - `Δ(e)` and `Δ(hx)` (`x ∈ [w]`) differ by `≤ c_2` by D(★), since `h[w] ⊆ [v]` has a common prefix `≥ n − |h| − 1`.
- **Upper bound, `|v| ≤ n + Δ + K_3`.**
  - Pick `y_1, y_2` in the state arc `s_n` whose next images lie in arcs `[P_i,P_{i+1})` with different `i`. This is
    possible from the explicit transitions, and there are finitely many choices.
  - Their rays from `F` split within a bounded time `D_sep` and then separate linearly.
  - So the rays from `hF` to `h u_w y_1`, `h u_w y_2` split within `n + D_sep`.
  - If the `F`-rays to these two points shared the tile at time `|v| > n + Δ + K_3`, Lemma D would keep the
    `hF`-rays `2c_1`-close at time `n + K_3 − c`, which is impossible for `K_3` large.
- **Conclusion.**
  - `hu_wF` is `c_1`-close to `τ_{n+Δ}(hx)`, and `u_vF = τ_{|v|}(hx)`.
  - So `d(F,kF) = d(u_vF, hu_wF) ≤ c_1 + max(K_2, K_3) + c_2 =: K`.

*Nucleus.*
- The local action of `h` at `[w]` is the map `y ↦ k·y` from the arc `s_n` to the arc of the last state of `v`, read on
  itineraries. It is determined by `(s_n, t(v), k)`.
- By Lemma E the deep local actions of every `h ∈ Γ` lie in the finite set `{states}² × B_K(1)`.
- The shallow cylinders are finitely many. So every `h` is rational, and the nucleus is finite.
- With Steps 2–4, `Γ ≅` a contracting RSG in `R_{Γ_BS, Σ}`. ∎

**Extension.** By `contracting-rsgs-closed-under-finite-index-overgroups` (and Selberg's lemma), the same holds for
every non-orientable closed hyperbolic surface group and every cocompact Fuchsian group.

## Referee (bh-ref-q11, 2026-09-18): PASS, with four repairs below (none changes the result)

**Checked at source.**
- Bowen–Series, Publ. IHÉS 50 (1979), NUMDAM scan pp. 159–163: Lemmas 2.2–2.4 and the proof of 2.4.
- Katok–Ugarcovici, arXiv:1610.00167v2, §1–§2: the (8g−4)-gon with all angles π/2 and the extension condition; σ(i); (1.6); (1.7); footnote 1 (exactness); Prop. 2.2, which matches the route verbatim.
- BBMZ arXiv:2309.06224v3, HTML: Question 1.1 verbatim, "Is every non-elementary hyperbolic group isomorphic to a contracting RSG?"; Def. 2.32 (RSG: canonical similarities between cones ⊊ E with t(α) = t(β)); Def. 2.41 (contracting = irreducible core plus finite nucleus).

**Steps 1–3: PASS.**
- The transitions for a_i and b_i follow from KU Prop. 2.2 and the order (1.6).
- Irreducibility follows directly from BS (Miii), proved in Lemma 2.5, even without exactness.
- The coding space is the union of the state cones. Adding one root vertex gives BBMZ's E.

**Step 4 (★): PASS, with repair (i).** BS state Lemma 2.4 as an exception "for the pairs (Q_i, g_{i−1}Q_i)". Their proof, however, reduces an arbitrary g to generator steps (z, g_j z) and shows every step is f-equivalent unless it is a badly matched pair at Q_i. So one Γ-orbit may split into several f-classes through intermediate exceptional steps; the exceptions are not isolated pairs. The conclusion B = Γ·Π still holds:
- Chain y = z_0, …, z_k = x by generators, with y ∈ Π.
- After the last exceptional step, x is f-equivalent to a point of {Q_i, g_{i−1}Q_i} ⊆ Π. Here g_{i−1}Q_i ∈ Π because g_{i−1}C(s_{i−1}) is an isometric circle with endpoints in Π.
- If there is no exceptional step, x is f-equivalent to y itself.
- Then f(Π) ⊆ Π (BS Lemma 2.3, with W = Π) gives x ∈ B.

**Step 5: PASS.** Lemmas A and B, the height argument of Lemma C, and the nucleus conclusion are all correct. The (★) points need:
- **(ii) Lemma E, lower bound.** Case-split on the comparison time t = lev(e) − Δ(e), not on lev(e). Lemma D is only available for t ≥ |h| + c, and lev(e) ≥ |h| + c does not give that when Δ > 0. Replace t by max(t, |h| + c): the F-ray stays in car(W) after lev(e), so C(★) still applies and gives lev(h^{-1}e) ≤ max(lev(e) − Δ, |h| + c) + K_1. The second branch then contradicts n ≥ n_0(h) ≥ |h| + c + K_1.
- **(iii) Lemma E, the common prefix.** The claim "h[w] has a common prefix ≥ n − |h| − 1" is not justified as stated. It does follow from (ii): |v| + 1 = lev(e) > n − |h| − K_1. So the bound is n − |h| − K_1 − 1, which is still ≥ |h| + c′ for n ≥ n_0(h), and that is all D(★) needs.
- **(iv) Lemma D(★).** Fix Δ(ξ) canonically, e.g. as the integer nearest the Busemann difference β_ξ(F, hF). Then |Δ(ξ) − Δ(ξ′)| ≤ c_2 whenever (ξ|ξ′)_F ≥ |h| + c′, by the standard continuity of Busemann functions on balls in δ-hyperbolic graphs. Stated in the node without proof; standard.
- **Upper bound in Lemma E.** Correct. Each state's f-image meets two letter arcs, e.g. T_i(a_i) = b_{σ(i)+1} ∪ a_{σ(i)+2}. The fixed pair y_1, y_2 has bounded Gromov product, and the needed time |v| − Δ ≥ |h| + c holds for n ≥ n_0(h).

**Priority / credit.** I found no prior statement that surface groups are contracting RSGs. Searches covered BBMZ, Belk–Bleak–Matucci "Rational embeddings of hyperbolic groups" (arXiv:1711.08369) and Bowen–Series-type literature (Mj–Mukherjee; Alvarez–Los on Bowen–Series-like maps). The coding is Bowen–Series' and Adler–Flatto's (the domain), with the Markov structure as presented by Katok–Ugarcovici. The contracting-RSG framework is BBMZ's. The new content is Lemmas A–E.

**Scope.** The result holds for closed orientable surfaces with Adler–Flatto's domain. The Extension corollary (cocompact Fuchsian groups) rests on `contracting-rsgs-closed-under-finite-index-overgroups`, which I did not referee.
