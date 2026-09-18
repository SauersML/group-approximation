---
rg: 2
id: torsion-free-cubulated-f-infinity-simple-host-proof
kind: route
title: Claimed proof that free cocompact cubulated groups embed in F_infinity simple groups, via free loops at every vertex, the flagged pointed-cube category, Cuntz stabilization, Li's Corollary D and Matui's simplicity theorem, plus a Krasner-Kaloujnine step for finite extensions
target: torsion-free-cubulated-groups-embed-in-f-infinity-simple-groups
requires:
  - flagged-pointed-cube-category-resynchronizes-cubulated-actions
  - flagged-pointed-cube-category-proof
  - cuntz-stabilized-garside-full-groups-are-f-infinity
  - cuntz-stabilized-garside-full-groups-f-infinity-proof
  - cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple
  - matui-purely-infinite-minimal-full-groups-have-simple-d
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
---

**Proof claimed, REPAIRED 2026-09-18 (sink characters, 866b27097a), not independently reviewed.**
Notation is that of the target. Throughout, `𝒢⁺ = I_l ⋉ X_∞` with `X_∞ = ∂Ω(C⁺) ∩ Ω_∞`,
basic open sets are those of `X_∞`, and every point is a Roller point.
- A proper cocompact action on a CAT(0) cube complex forces local finiteness and finite
  dimension.
- The tree of copies `T` has as vertices the copies of `X` in `X'`, and as edges the
  `c`-edges. `X'` is simply connected, so `T` is a tree. `G'` acts on `T` with trivial
  edge stabilizers, because it acts freely on the edges of `X'`.

## 1. Fresh exits

**Lemma E′** (replaces the original Lemma E, which referee bh-ref-q115-a showed false when
`B` has holes whose witness walls lie beyond the first cube; the repair is theirs, written out
here). Let `B = λ·X(v;e)` be a nonempty basic open subset of `X_∞`, ending at `(p,μ)`, with
holes `f = (u_f, τ_f) ∈ e` (one-step morphisms from `(p,μ)`). Pick a Roller point `ω_0 ∈ B`.
- **Why `ω_0` avoids each hole.** Since `ω_0 ∈ B`, for each `f ∈ e` either
  `u_f ∉ I(p,ω_0)`, or `u_f ∈ I(p,ω_0)` and `ω_0` crosses a **witness wall**
  `K_f ∈ τ_f ∩ H(u_f,ω_0)`.
- **Choice of `q`.** Choose a vertex `q` on a geodesic ray of `ω_0` from `p` beyond:
  - (i) every crossing of a wall of `adj(p)` that `ω_0` crosses;
  - (ii) the crossing of each witness wall `K_f`.

  If `q` is entered by a `c`-edge, move `q` one step further along the ray. If the ray's
  next step is also a `c`-edge, then instead leave the ray by one internal edge of the new
  copy. That edge is allowed, because after a `c`-edge the only forbidden wall is the
  `c`-wall behind it, and `ω_0` has already passed (i) and (ii).
- **Then:**
  - Both `c`-edges at `q` are allowed. Their walls are adjacent only to `q` and its
    `c`-neighbours, and `q` was entered by a non-`c` edge, so these walls are neither crossed
    nor propagated labels.
  - Let `ω'` follow `ω_0`'s path (or the one-edge detour) to `q`, then take either `c`-edge,
    then anything in that branch. Then `ω' ∈ B`:
    - it crosses exactly the walls of `adj(p)` that `ω_0` crosses, so `u_f ∈ I(p,ω')` iff
      `u_f ∈ I(p,ω_0)`;
    - it crosses each witness `K_f` after `u_f`;
    - it never crosses a wall of `μ`, since after `q` it stays in a branch disjoint from
      `p`'s copy and from the other `c`-edges at `p`.
  - From the landing vertex, every vertex of the new copy is a geodesic continuation. So
    every end of the branch beyond either `c`-edge at `q` is realized in `B`.

## 2. (TF), faithfulness, Hausdorff and effective

- **(TF).** Suppose `k ∈ G'` fixes a nonempty open subset of `∂_R X'` pointwise.
  - By Lemma E′, `k` fixes every end of a half-tree of `T` beyond a `c`-edge.
  - That half-tree has infinitely many ends, so `k` fixes the edge.
  - Edge stabilizers are trivial, so `k = 1`.
  - Cones of objects embed as open subsets of the base cone, so (TF) also holds on every
    cone.
- **Faithfulness** follows from (TF).
- **The inverse hull.** `C⁺` has lcms, so every element of Li's inverse hull is `λμ^{-1}`
  or `0`.
- **Hausdorff and effective.** For `λ ≠ μ`, `λμ^{-1}` is the identity on no open set: by
  §3 of `flagged-pointed-cube-category-proof` it acts as a nontrivial element of `G'`
  there, which (TF) forbids. So the set where a germ is a unit germ is empty or
  everything. Hence `𝒢⁺` is Hausdorff and effective (essentially principal).

## 3. The bisection embedding

By item 3 of `flagged-pointed-cube-category-resynchronizes-cubulated-actions`, every `g ∈ G'`
is a global bisection of `𝒢⁺|_Y`. By §2 the map `G' → F(𝒢⁺|_Y)` is injective. Then
`g ↦ g × id` embeds `G'` in `S`.

## 4. (Acyc), and finiteness

Take a non-unit loop `σ ∈ C⁺(v,v)` with `v = [(w,λ)]`.
- **The loop moves.** `σ = (w,λ; hw,hλ)` with `h ≠ 1`: a flag has a different domain
  object, and `h = 1` would force `σ` to be the identity. So `∩_m σ^m X(v)` consists of
  points crossing every wall of `W = ∪_m H(w, h^m w)`.
- **An escaping point in any open set.** Take a basic open `B ⊆ X(v)`, and pick `q` and
  its two `c`-edges as in Lemma E′.
  - If `h` fixes a copy `X_0` in `T`, then `W` is an infinite set of walls of `X_0`. Take
    the `c`-edge at `q` whose branch misses `X_0`.
  - Otherwise `h` translates along an axis of `T` towards an end `ξ`, and `W` contains
    infinitely many `c`-walls on the way to `ξ`. Take the `c`-edge at `q` whose branch
    misses `ξ`. The two branches at `q` are disjoint, so one of them works.
  - The resulting point of `B` crosses only finitely many walls of `W`.
- **Conclusion.** So `∩_m σ^m X(v)` has empty interior, and (Acyc) holds. `C⁺` is
  Li-Garside with trivial units (item 1 of the flag theorem). So
  `cuntz-stabilized-garside-full-groups-are-f-infinity` makes `S` of type `F_∞`.

## 5. Minimal, purely infinite, acyclic, simple

**Minimal.** Take `ω ∈ Y` and a basic open `B ⊆ Y` ending at `(p,μ)`. Choose any object
`(z_n,κ_n)` on the tail of `ω` with `κ_n ≠ ∅`, and `e ∈ κ_n`. Let `v''` be the vertex of `K`
under the endpoint of `e` opposite `z_n`.
- By Lemma E′, go from `p` to `q` and through a `c`-edge into a fresh copy.
- Walk inside it (the whole copy is allowed) to a vertex over `v''`, and take `c_{v''}`
  into another fresh copy, landing at `q''` over `v''`.
- Cross the edge at `q''` matching `e`. This reaches a translate `z''` of `z_n` with
  natural label `{e''}`, since the `c`-wall is not adjacent to `z''`.
- Flag up to the translate of `κ_n`.
- Append the tail of `ω`. This gives a point of `B` in the orbit of `ω`.

**Purely infinite.** Any clopen `A ⊆ Y × {x,y}^ℕ` is a finite disjoint union of rectangles
`B × C_w`. The maps `(y,wx) ↦ (y,w0x)` and `(y,wx) ↦ (y,w1x)` witness proper infiniteness
(Matui's definition). The product is minimal because both factors are.

**Comparison.** Use Li's pure-infiniteness criterion: for clopen `U` and `V ≠ ∅`, take
`V ⊇ B × C_w`. By minimality and compactness, `U = ⊔_j U_j` with compact open bisections
`σ_j` of `𝒢⁺` carrying `pr(U_j)` into `B`. Send `U_j` into `B × C_{w u_j}`, with `u_j`
pairwise incomparable words. This is Step 3 of
`cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`, with bisections in place of
group elements.

**Acyclic and simple.**
- Matui's Künneth formula with `H_*(G_2) = 0` gives `H_*((𝒢⁺ × G_2)|_{Y×C}) = 0`.
- The unit space is a Cantor set.
- Li's Corollary D (quoted verbatim on main) gives that `S` is integrally acyclic and
  perfect.
- `𝒢⁺ × G_2` is essentially principal, since both factors are effective. Matui's
  Theorem `simple2` makes `D(S)` simple. So `S = D(S)` is simple.

## 6. Finite extensions

Let `G` be virtually torsion-free and cubulated, and let `G_0 ⊴ G` be torsion-free of finite
index (the normal core of a torsion-free subgroup). Put `Q = G/G_0`.
- `G_0` acts freely and cocompactly, so `G_0 ≤ S` as above.
- By Krasner–Kaloujnine, `G ↪ G_0 ≀ Q ≤ S ≀ Q`.
- Choose a prefix code `{w_q}` of size `|Q|` in `{x,y}^*`. Then `S` restricted to
  `Y × C_{w_q}` is a copy of `S`, extended by the identity. The copies commute, and the
  bisection `(y,w_q x) ↦ (y, w_{π q} x)` permutes them.
- So `S ≀ Q ≤ S`, and `G ≤ S`. ∎

## Checklist for referees

1. Lemma C and the lcm formula of `flagged-pointed-cube-category-proof`.
2. The head and normal form argument there, and the claim that `(𝔖⁺^{≤L})^♯` is closed
   under left divisors.
3. The maximal-character identification (the minimal-`J` gate argument).
4. The germ formula (item 3).
5. The Cuntz theorem's use of Li's lemma, read over `Γ(*)`.
6. Lemma E′ and (Acyc).
7. The hypotheses of Li's Corollary D and Matui's Theorem `simple2` for this groupoid.

## Lesson for general BH

A hard embedding problem became three orthogonal local repairs, each adding one kind of
generator:
- a flag (a promise about the future);
- a Cuntz letter (a copy for packing);
- a free loop (an exit for dynamics).

The generic template for Boone–Higman on geometric groups is to find the finite local state,
add promise moves until codings from different base points resynchronize, then stabilize
by Cuntz and by free exits.

## Referee A note on Lemma E (bh-ref-q115-a, 2026-09-18)

**Lemma E is false as stated when `B` has holes.**
- *Counterexample.* Let `f ∈ e` be the one-step morphism along `s_0` with label
  `τ_f = π(μ;p,p') ∪ {K}`, where `K ∈ adj(p')` is a wall that `ω_0` crosses after `p'`. Then
  `ω_0 ∉ f·X(𝐝 f)`. But a continuation that leaves `p'` at once through a `c`-edge never
  crosses `K`, so it lies in `f·X(𝐝 f)` and not in `B`.
- *Worse case.* Take holes `f_s` for every first cube `s`, each forbidding every non-`c` wall at
  the far corner. Then `B` is still nonempty, but no immediate `c`-exit lies in `B`.

**Lemma E′ (repair).** Choose `q` on the path of `ω_0` after:
- (i) every wall of `adj(p)` that `ω_0` crosses;
- (ii) for every hole `f ∈ e` with `u_f ∈ I(p,ω_0)`, a witness wall
  `K_f ∈ τ_f ∩ H(u_f,ω_0)`.

Choose `q` so that it is entered by a non-`c` edge, taking one internal step in its copy if
needed. Then continue through a `c`-edge at `q` that `ω_0` does not use.
- The continuation crosses exactly the walls of `adj(p)` that `ω_0` crosses, so `u_f ∈ I(p,·)`
  is unchanged.
- It crosses every `K_f` after `u_f`, and it never crosses `μ`. So it lies in `B`.
- Every Roller point of the new branch is realized in `B`.

(TF), (Acyc) (use `q` in place of `p'` and the same two-branch choice at `q`) and the minimality
walk then go through verbatim. This also covers referee B's case where `s_0` is a `c`-edge.
