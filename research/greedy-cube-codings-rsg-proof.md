---
rg: 2
id: greedy-cube-codings-rsg-proof
kind: route
title: Pairwise crossing of separating hyperplanes at a vertex gives the Markov property; a vertex-free action gives canonical similarities in G; heights over carriers plus (NA) give injectivity and uniform carrier entry, and the referee-repaired surface Lemmas D–E give a finite nucleus
target: greedy-cube-codings-make-cubulated-hyperbolic-groups-rsgs
requires:
  - closed-surface-groups-are-contracting-rsgs
  - sft-irreducible-core-iff-unique-recurrent-component
---

Lane `bh-partials`, lane proof, not reviewed. Rewritten 2026-09-19. The first version stated Steps 3–4 in outline; they
are now proved in full, with repairs (ii)–(iv) of the referee of `closed-surface-groups-contracting-rsg-via-bowen-series`
carried over.

## Setting and notation

- `G` is hyperbolic and acts on a locally finite CAT(0) cube complex `X`, cocompactly and freely on vertices. `X^{(1)}` is
  `δ`-hyperbolic.
- `G` acts faithfully on `∂G`; equivalently, its finite radical is trivial.
- Edge inversions are allowed. A `G`-equivariant total order on the edges at each vertex exists: order at orbit
  representatives and transport it.
- Distances are combinatorial, and a combinatorial geodesic crosses every hyperplane at most once.
- `N(H)` is the carrier of `H`, a convex subcomplex. For a vertex `y`, the hyperplanes separating `y` from `N(H)` are
  exactly those separating `y` from its gate in `N(H)`, and none of them meets `N(H)`.
- `∂X` is the Roller boundary: the non-principal ultrafilters. It is compact and totally disconnected.
- For `ω ∈ ∂X` and a vertex `y`, `S(y,ω)` is the set of edges at `y` whose hyperplanes separate `y` from `ω`.
- `R_a(ω)` is the **greedy ray** from `a`: repeatedly cross the smallest edge of `S(·,ω)`. By equivariance of the order,
  `gR_a(ω) = R_{ga}(gω)`.
- A **directed ray** toward `ω` is any combinatorial geodesic ray that crosses only hyperplanes separating its current
  vertex from `ω`. Greedy rays are directed rays.
- **(NA)** For disjoint hyperplanes `H, K`, `Stab(H) ∩ Stab(K)` is finite.

## Step 1 (Markov; no hypothesis)

- **Quarter lemma.** Let `H ≠ L` be hyperplanes dual to edges at `x` that do not cross, with `x ∈ H^- ∩ L^-`. The
  neighbours of `x` across `H` and across `L` lie in `H^+ ∩ L^-` and `H^- ∩ L^+`, so `H^+ ∩ L^+ = ∅`.
- **So the hyperplanes of `S(x,ω)` pairwise cross.** An ultrafilter picks pairwise intersecting halfspaces. So `S(x,ω)`
  spans a cube at `x`. Also, if `ω ∈ H^+`, no edge at `x` whose hyperplane misses `H` lies in `S(x,ω)`.
- **The pieces.** Let `e = min S`, with hyperplane `H`, and let `x_1` be its far end. The edges at `x` crossing `H` span
  squares with `e`, so they correspond to edges at `x_1` with the same hyperplanes. Hence, for `ω` with
  `S(x_1, ω) = S'`, we have `S(x,ω) = S` iff `e^{-1} ∉ S'` and `S' ∩ cross(H) = S ∖ {e}`. The edges at `x_1` whose
  hyperplanes miss `H` impose nothing: by the quarter lemma they never separate `x` from `ω ∈ H^+`.
- **The state graph `𝒢`.** Translating by the unique `g` with `g x_1 = rep(x_1)` gives `𝒢` on the finitely many states
  `(rep, S)` with nonempty piece. The greedy map is injective on each piece.
- **Cylinders.** The cylinder of an admissible word `w` is `[w] = u_w(A_{t(w)})`, where `u_w ∈ G` carries `rep` to the
  end vertex of the word.

## Step 2 (RSG)

For cylinders `[w]` and `[w']` with the same terminal state, `u_{w'}u_w^{-1} ∈ G` maps `[w]` onto `[w']` and preserves
tails. This is BBMZ Def. 2.32.

## Step 3 (heights, injectivity, the map to `∂G`; under (NA))

**Lemma H (height).** Let `R` be a directed ray toward `ω`, with `ω ∈ H^+` and `R(0) ∈ H^-`. Put
`h(t) = d(R(t), N(H))`.
- `h` never increases. It drops by 1 exactly when `R` crosses a hyperplane separating `R(t)` from `N(H)`, and it is
  unchanged when `R` crosses a hyperplane crossing `H`.
- **Proof.**
  - Let `L` be the next crossed hyperplane.
  - If `L` misses `H` and does not separate `R(t)` from `N(H)`, then `N(H) ⊂ L^-`. `L` is dual to an edge with both ends
    in `H^-`, so `L ⊂ H^-`. Hence `L^+ ⊂ H^-`. But `ω ∈ L^+` and `ω ∈ H^+`, a contradiction.
  - Every `K` separating `R(t)` from `N(H)` satisfies `K ⊂ H^-` and `H^+ ⊂ K^+`, so it separates `R(t)` from `ω`.
  - A hyperplane crossing `H` meets `N(H)`, so it separates nothing from `N(H)`.

**Lemma B (bounded coarse intersections).** For every `c` there is `D_0(c)` such that, for disjoint hyperplanes `H, K`,
the set `B(H,K,c) = {y : d(y,N(H)) ≤ c, d(y,N(K)) ≤ c}` has diameter `≤ D_0(c)`.
- **Infinite diameter gives a ray.** Carriers are convex, so a geodesic between two points of `B` stays within `c + 2δ`
  of both carriers (thin quadrilaterals through the gates). An unbounded `B` therefore gives, by Arzelà–Ascoli, a
  geodesic ray `y_t` within `c + 2δ` of `N(H)` and `N(K)`.
- **The ray contradicts (NA).**
  - Choose `g_t` with `g_t y_t` in a finite set of orbit representatives.
  - The pairs `(g_tH, g_tK)` are pairs of hyperplanes within `c + 3` of that set, so they are finitely many.
  - So infinitely many `t` share `(g_tH, g_tK, g_ty_t)`. For such `s ≠ t`, `g_s^{-1}g_t ∈ Stab(H) ∩ Stab(K)` sends
    `y_t` to `y_s`, and these elements are pairwise distinct.
- **Uniformity.** Up to `G` there are finitely many pairs `(H,K)` with `B(H,K,c) ≠ ∅`, so the bound is uniform.

**Lemma C (carriers are entered).** Let `R` be a directed ray toward `ω ∈ H^+`.
- **(i)** `R` meets `N(H)`.
- **(ii) Quantitative.** If `d(R(t_0), N(H)) ≤ c`, then `R` meets `N(H)` by time `t_0 + D(c)`, with
  `D(c) = c(D_0(c) + 1)`.
- **Proof of (ii).**
  - While `h > 0`, the current vertex lies within `h ≤ c` of `N(H)`.
  - It also lies within `h` of `N(K)`, for one of the at most `c` hyperplanes `K` separating `R(t_0)` from `N(H)`: the
    geodesic to the gate crosses `K`. So it lies in `B(H,K,c)`.
  - A geodesic spends at most `D_0(c) + 1` steps in each such set.
- **Proof of (i).**
  - If `h` stays at some value `h_∞ > 0`, then from some time on `R` crosses only hyperplanes crossing `H`.
  - Then `R` lies in `B(H,K,h_∞)` for a fixed separating `K`, which is bounded by Lemma B. A geodesic ray cannot stay in
    a bounded set.
- **After entry.** Once `R` is in `N(H)`, it crosses only hyperplanes crossing `H`, or `H` itself (Lemma H with
  `h = 0`, and the quarter lemma). So it stays in `N(H)` until it crosses `H`.

**Lemma I (injectivity).**
- Let `ω ≠ ω'` have the same itinerary. They share one greedy ray `R` and its states, and they differ on some
  hyperplane `H`, say `ω ∈ H^+ ∌ ω'`.
- `R` never crosses `H`: that would need `H` to separate it from both.
- By Lemma C(i), applied toward whichever point lies across `H` from `R(0)`, `R` meets `N(H)` at some vertex `y`. There
  `S(y,ω) ≠ S(y,ω')`, a contradiction.
- The itinerary map is continuous. Surjectivity holds because admissible cylinders are nonempty compact sets, and a
  nested intersection of nonempty compact sets is nonempty. So `∂X ≅ Σ_𝒢`, `G`-equivariantly.

**Lemma Z (the map to `∂G`).** Every directed ray toward `ω` converges in `∂G`, and all of them converge to the same
point `ζ(ω)`. Consequences:
- `ζ(gω) = gζ(ω)`, so `ζ` is `G`-equivariant.
- `ζ` is onto: a geodesic ray from `x_0` to any `ξ ∈ ∂G` is directed toward the ultrafilter of its eventual sides.
- `G` acts faithfully on `∂X`, because it does on `∂G`.

*Proof of Lemma Z.*
- **Setup.** Let `R_1`, `R_2` be directed rays toward `ω` with limit points `ξ_1 ≠ ξ_2`; they converge because they are
  geodesic rays. Let `γ` be a bi-infinite geodesic from `ξ_1` to `ξ_2`.
- **Few crossed hyperplanes contain `ξ_2` in their limit set.** By (NA) and Lemma B, the hyperplanes crossed by `γ` whose
  limit sets contain `ξ_2` pairwise cross. So there are at most `dim X` of them, and likewise for `ξ_1`.
- **Choosing `H`.** Local finiteness then gives a hyperplane `H`, crossed by `γ` far out, with three properties:
  `ξ_1, ξ_2 ∉ Λ(H)`; `R_1(0)` and `R_2(0)` lie on the `ξ_1`-side `H^-`; and `ξ_2` lies in `Λ(H^+) ∖ Λ(H)`.
- **The contradiction.**
  - `R_2` ends in `H^+`, so it crossed `H`, and `ω ∈ H^+`.
  - By Lemma C, `R_1` meets `N(H)`. Afterwards it either stays in `N(H)`, so `ξ_1 ∈ Λ(H)`, or crosses `H`, so
    `ξ_1 ∈ Λ(H^+)`.
  - Both contradict the choice of `H`, since `Λ(H^+) ∩ Λ(H^-) = Λ(H)`.

## Step 4 (finite nucleus; under (NA) and (P2))

- **(P2).** Every piece contains two points with distinct `ζ`. It follows from (IRR): if a core piece had a one-point
  image, every core piece would, since core pieces contain translates of one another. Every point lies in a translate
  `u_w(A_σ)` of a core piece, so `ζ(∂X)` would be countable, contradicting `ζ` onto. Non-core pieces contain translates
  of core pieces.
- **Lemma D (from the surface route, repair (iv)).** Fix `h`, and put `r = d(x_0, hx_0)`. For `ξ ∈ ∂G`, let `Δ(ξ)` be the
  integer nearest `β_ξ(x_0, hx_0)`. Then:
  - `d(R_{x_0}(ω)(t + Δ), R_{hx_0}(ω)(t)) ≤ c_1` for `t ≥ r + c`, where `Δ = Δ(ζ(ω))`;
  - `|Δ(ξ) − Δ(ξ')| ≤ c_2` whenever `(ξ|ξ')_{x_0} ≥ r + c'`.

  The constants depend on `δ` only. This is standard for asymptotic rays in `δ`-hyperbolic graphs.

**Lemma E.** Fix `h`. For `n ≥ n_0(h) := r + c + c' + D(c_1) + 2K_0`, let `[w]` be a cylinder of depth `n` ending at
`y_n = u_wx_0`, let `[v] ⊇ h[w]` be the smallest cylinder containing it, with `m = |v|` and `z = u_vx_0`, and put
`k = u_v^{-1}hu_w`. Then `d(x_0, kx_0) = d(z, hy_n) ≤ K`, where `K` does not depend on `h`.

**Lower bound.**
- **A separating hyperplane.** By minimality, two points `hω, hω'` of `h[w]` have different states at `z`. So some `W*`
  adjacent to `z` separates them.
- **The `h`-rays avoid its carrier up to time `n`.** `h^{-1}W*` separates `ω` from `ω'`. Their rays from `x_0` share
  states up to `y_n`, so `h^{-1}W*` is adjacent to none of `y_0, …, y_n`. Hence `B := hR_{x_0}(ω'') = R_{hx_0}(hω'')`
  avoids `N(W*)` up to time `n`, for both `ω'' ∈ {ω, ω'}`.
- **Choice of target.** Pick `ω''` with `hω''` across `W*` from `hx_0`. Let `A := R_{x_0}(hω'')`,
  `Δ := Δ(ζ(hω''))`, and `t* := max(m − Δ, r + c)`.
- **At time `t* + Δ ≥ m`, `A` is in `N(W*)` or on the `hω''`-side of `W*`.** This holds by Lemma C and "after entry",
  since `A(m) = z ∈ N(W*)`.
- **`B` enters the carrier soon.** If `B(t*)` has not met `N(W*)`, it lies on the other side, within `c_1` of
  `A(t* + Δ)`. So `d(B(t*), N(W*)) ≤ c_1`, and by Lemma C(ii) `B` meets `N(W*)` by time `t* + D(c_1)`.
- **Conclusion.** So `n < t* + D(c_1)`. For `n ≥ n_0(h)` this forces `t* = m − Δ`, that is, `m > n + Δ − D(c_1)`
  (repair (ii)).

**Common prefix (repair (iii)).**
- `m ≥ n − r − D(c_1) − K_0`, where `|Δ| ≤ r + K_0`.
- So all points of `h[w]` have pairwise Gromov products at `x_0` of at least `m − 2δ ≥ r + c'`.
- By Lemma D, their shifts `Δ` agree within `c_2`.

**Upper bound.**
- **Two diverging points.** By (P2), fix for each state `σ` two points `p_σ, p'_σ` of its piece with
  `(ζp_σ|ζp'_σ)_{x_0} ≤ g_0`. Let `q = u_wp_{σ_n}` and `q' = u_wp'_{σ_n}`, both in `[w]`.
- **Estimate from `hx_0`.** `(ζhq|ζhq')_{hx_0} ≤ n + g_0 + 2δ`, since the `h`-rays agree exactly up to `hy_n`.
- **Change of basepoint.** Up to `O(δ)`,
  `(ξ|ξ')_{x_0} = (ξ|ξ')_{hx_0} + (β_ξ(x_0,hx_0) + β_{ξ'}(x_0,hx_0))/2`.
- **Estimate from `x_0`.** `(ζhq|ζhq')_{x_0} ≥ m − 2δ`, since the rays from `x_0` share `m` steps.
- **So** `m ≤ n + Δ + K_3`, with `K_3 = g_0 + c_2 + O(δ)`.

**Conclusion.** `d(z, hy_n) ≤ d(A(m), A(n + Δ)) + d(A(n + Δ), hy_n) ≤ max(D(c_1), K_3) + c_2 + c_1 =: K`.
- The local action of `h` at `[w]` is `ξ ↦ kξ`, from the piece of `σ_n` to the piece of `t(v)`.
- So the deep local actions of all `h ∈ G` lie in the finite set `{states}² × B_K(x_0)`.
- The shallow cylinders are finitely many, so every `h` is rational and the nucleus is finite.

## Step 5 (contracting)

Under (IRR), the unique recurrent component is an irreducible core
(`sft-irreducible-core-iff-unique-recurrent-component`). Its path space has no isolated points: an isolated point would be a cylinder
`u_w(A_σ)` with a single point, against (P2). With Steps 2–4, `G` is a contracting
RSG (BBMZ Def. 2.41). ∎

## For the referee

- Lemma B's uniformity.
- The choice of `H` in Lemma Z. It uses `Λ(H^+) ∩ Λ(H^-) = Λ(H)` and the `dim X` bound on pairwise crossing families.
- Lemma E's constants.

## Referee (bh-ref-q11, 2026-09-19): PASS, with three nits

**Read in full.** Steps 1–5 and every lemma.

**Verified.**
- **Quarter lemma and Markov formula.** Includes the identification of the edges at `x` and at `x_1` that cross `H`, via the squares on `e`.
- **Lemma H.** In the case "`L` misses `H` and does not separate": `L ⊂ H^-` and `H ⊂ L^-` give `L^+ ⊂ H^-`, which contradicts `ω ∈ L^+ ∩ H^+`.
- **Lemma B.** The thin-quadrilateral step and Arzelà–Ascoli. The `(NA)` contradiction: the elements `g_s^{-1}g_t` are pairwise distinct because the vertex action is free. Uniformity: finitely many pairs up to `G`.
- **Lemma C.** Both parts, and "after entry".
- **Lemma I.** It needs only Lemma C(i), not `ζ`.
- **Lemma Z.**
  - Disjoint hyperplanes whose limit sets share `ξ` would give an unbounded `B(H,K,c)`. So at most `dim X` crossed hyperplanes contain a given endpoint (Helly).
  - `Λ(H^+) ∩ Λ(H^-) = Λ(H)` holds because a geodesic between sequences on the two sides meets `N(H)` near `ξ`.
  - The choice of `H` and the contradiction are correct.
  - It gives `ζ` equivariant and onto, and a faithful `G`-action on `∂X`.
- **(P2) from (IRR).** A one-point core piece would make `ζ(∂X)` countable.
- **Lemma E.**
  - Choosing `ω''` across `W*` from `hx_0`, together with "in `N(W*)` or on the `hω''`-side after time `m`", is exactly the repair that the 3D node `right-angled-h3-reflection-rsg-via-greedy-roller-coding` needed. There the targets need not lie on the wall.
  - Upper bound, change of basepoint and conclusion: correct.
- **Remark 2.4 for `Σ_𝒢`.** No empty cones, since every nonempty piece has a successor. No isolated points, by (P2) applied to every piece, not only core pieces.

**Nits (none changes the result).**
- **(N1) Off by one in Lemma E.** `[v]` fixes the state at `z = u_vx_0`. Minimality therefore makes the points of `h[w]` differ at the *next* vertex `z⁺ = A(m+1)`, and `W*` is adjacent to `z⁺`. Replace `m` by `m+1` in the lower bound; `K` grows by 1.
- **(N2) `n_0(h)` is too small for the common-prefix step.** `m ≥ n − r − D(c_1) − K_0` and `m − 2δ ≥ r + c′` need `n ≥ 2r + c′ + D(c_1) + K_0 + 2δ`. Take `n_0(h) := 2r + c + c′ + D(c_1) + 2K_0 + 2δ + 1`. `n_0` may depend on `h`, so nothing else changes.
- **(N3) Lemma C's hypothesis.** It needs `R(0) ∈ H^-`, as Lemma H assumes. Every use satisfies this: Lemma I (target across `H`), Lemma Z (`R_1(0) ∈ H^-`) and Lemma E (`hω''` across `W*` from `hx_0`).

**Standard inputs recalled, not re-derived.**
- Pairwise crossing hyperplanes at a vertex span a cube (flag links, no inter-osculation).
- Hyperplane stabilizers act cocompactly on carriers and are quasiconvex.
- `Λ(A) ∩ Λ(B) = Λ(A ∩ B)` for quasiconvex `A, B`. This is used only for the remark that (NA) is equivalent to disjoint limit sets.
- Lemma D: asymptotic rays and Busemann shifts in `δ`-hyperbolic graphs.

**Credit.** The mechanism is Bowen–Series (1979) transplanted to cube complexes. The main inputs are Sageev's and Roller's duality and boundary, the Niblo–Reeves pairwise-crossing lemma, and BBMZ's RSG framework. The hyperbolic-geometry lemmas are standard (Gromov; Coornaert–Delzant–Papadopoulos). Coornaert–Papadopoulos (1993) already code `∂G` of every hyperbolic group as a quotient of an SFT. What is new here is a coding that is injective on the Roller boundary and whose canonical similarities are group elements.
