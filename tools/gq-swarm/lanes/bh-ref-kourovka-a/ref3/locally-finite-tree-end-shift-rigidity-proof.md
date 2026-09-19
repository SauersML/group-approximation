---
rg: 2
id: locally-finite-tree-end-shift-rigidity-proof
kind: route
title: The descent rule makes every quantum idempotent depend only on the vertex it names, the edge rule makes each edge carry a projection and its complement, and the free-group chain argument then runs on the tree itself
target: locally-finite-tree-end-shifts-are-quantum-rigid-sfts
requires:
  - free-group-boundary-shifts-are-quantum-rigid
  - fp-v-times-subshift-full-groups-force-quantum-rigidity
---

Notation as in the target: `Λ`, `S`, `T`, the orbit representatives `v_1, …, v_r`, the finite generating
sets `K_i` of `Stab(v_i)`, the edge-orbit representatives `ε_0 = {v_i, h v_j}`, the rules (R1), (R2), and
`D_0`. Every edge of `T` is `g ε_0` for exactly one representative `ε_0` and some `g ∈ Λ`, since the
action has no inversions.

## §1. Coding (item 1)

- **Out-edges are well defined.** Let `x ∈ X_T`. For a vertex `w = g v_i` put `o(w) = g · x(g)_i`.
  - If also `w = g' v_i`, then `g' = gk` with `k ∈ Stab(v_i)`. Write `k` as a word in `K_i ∪ K_i^(-1)`.
  - (R1) gives `x(gk)_i = k^(-1) x(g)_i` one letter at a time; for `k^(-1)` apply (R1) at `gk^(-1)`.
  - So `g' x(g')_i = g x(g)_i`, and `o` is well defined.
- **Each edge is chosen by exactly one endpoint.** For an edge `ε = g ε_0` with `ε_0 = {v_i, h v_j}`,
  its endpoints are `g v_i` and `g h v_j`. (R2) at the site `g` says exactly one of `o(g v_i) = ε` and
  `o(g h v_j) = ε` holds. Any other expression `ε = g' ε_0` gives the same two statements, since `o` is
  well defined.
- **Configurations are ends.** So `o` picks exactly one out-edge at every vertex, and every edge is
  oriented consistently. Step 0 of `free-group-boundary-shift-rigidity-proof` applies verbatim on the
  tree `T`: the out-edge paths are rays, and any two share a tail. This defines an end `ξ(x)`.
- **Ends are configurations.** Conversely, for an end `ξ` let `x_ξ(g)_i = g^(-1) e`, where `e` is the
  first edge of the ray from `g v_i` to `ξ`. It satisfies (R1) and (R2).
- **Homeomorphism.** `x ↦ ξ(x)` is a `Λ`-equivariant bijection, since `(λx)(g) = x(λ^(-1) g)` moves every
  out-edge by `λ`. It is continuous, because a cylinder condition on finitely many sites is a condition on
  finitely many out-edges, which is open in `∂T`. A continuous bijection of compact Hausdorff spaces is a
  homeomorphism.
- **Finite type.** There are finitely many rules, each on two sites at distance at most `D_0`.

## §2. Descent of a quantum family

Fix `D ≥ D_0`, a field `k`, and a `D`-quantum family `E_c(g)` (`c ∈ A`, `g ∈ Λ`) on `W`.
- **Marginals.** For `e ∈ E(v_i)` put `O_i(g; e) = Σ_(c : c_i = e) E_c(g)`. By (Q1) these are orthogonal
  idempotents summing to `I` for each `(g, i)`, and they commute with one another at the same site.
- **Reduction.** `E_c(g) = ∏_i O_i(g; c_i)`, since the `E_c(g)` are orthogonal. So it suffices to show
  that all the `O_i(g; e)` commute.

**Lemma 1 (forbidden pairs vanish).** Let two sites `g, g'` with `d(g, g') ≤ D` and letters with
`O_i(g; e)`, `O_j(g'; e')` be such that no point of `X_T` has `x(g)_i = e` and `x(g')_j = e'`. Then
`O_i(g; e) O_j(g'; e') = 0`.
- *Proof.* Every idempotent at a site of `gB_D` commutes with every other there, by (Q2), since `gB_D`
  has diameter at most `2D`. Every pattern on `gB_D` that extends the pair `(e, e')` is forbidden, so its
  product vanishes by (Q3).
- Summing over all such patterns, and using (Q1) at the other sites, gives
  `O_i(g; e) O_j(g'; e') · ∏ I = 0`. ∎

**Lemma 2 (descent).** For `k ∈ Stab(v_i)` and `e ∈ E(v_i)`, `O_i(gk; k^(-1) e) = O_i(g; e)`.
- *First, `k ∈ K_i`.* By (R1) and Lemma 1, `O_i(g; e) O_i(gk; e') = 0` whenever `e' ≠ k^(-1) e`. Hence
  - `O_i(g; e) = O_i(g; e) Σ_(e') O_i(gk; e') = O_i(g; e) O_i(gk; k^(-1) e)`;
  - `O_i(gk; k^(-1) e) = Σ_(e'') O_i(g; e'') O_i(gk; k^(-1) e) = O_i(g; e) O_i(gk; k^(-1) e)`, because
    `k^(-1) e'' ≠ k^(-1) e` for `e'' ≠ e`.

  The two right sides agree, since the sites `g` and `gk` are within distance `D_0 ≤ 2D`, so the factors
  commute.
- *In general.* Induct on the length of `k` as a word in `K_i ∪ K_i^(-1)`. The inverse letters follow
  from the case just proved, applied at the site `g k^(-1)`. ∎

**Definition.** For a vertex `w` of `T` and an edge `ε` at `w`, choose `g` and `i` with `w = g v_i` and put
`O_w(ε) = O_i(g; g^(-1) ε)`. By Lemma 2 this does not depend on `g`. By (Q1), `{O_w(ε)}_(ε ∋ w)` is a
family of orthogonal idempotents summing to `I`.

## §3. The edge identity

**Lemma 3.** For every edge `ε = {w, w'}`, `O_w(ε) + O_(w')(ε) = I`.

*Proof.* Write `ε = g ε_0` with `ε_0 = {v_i, h v_j}`. Put `P = O_w(ε) = O_i(g; ε_0)` and
`R = O_(w')(ε) = O_j(gh; h^(-1) ε_0)`. The sites `g` and `gh` are within `D_0`, so `P` and `R` commute.
- "Both" is forbidden by (R2), so Lemma 1 gives `PR = 0`.
- "Neither" is forbidden by (R2). Summing Lemma 1 over the letters `e ≠ ε_0` at `g` and
  `e' ≠ h^(-1) ε_0` at `gh` gives `(I − P)(I − R) = 0`.
- So `I − P − R + PR = 0`, and with `PR = 0` this is `P + R = I`. ∎

## §4. Chains (item 2)

The families `{O_w(ε)}` on the vertices of `T` satisfy exactly the two inputs of Steps 2–3 of
`free-group-boundary-shift-rigidity-proof`:
- at each vertex, orthogonal idempotents summing to `I`, one per edge;
- on each edge, one idempotent and its complement (Lemma 3).

Those steps use nothing else: no group structure, no degree bound, no other commutation. They show:
- along a geodesic `w_0, …, w_n`, the backward idempotents form a commuting increasing chain;
- every label idempotent at `w_a` commutes with every label idempotent at `w_b`.

Any two vertices of `T` are the ends of a geodesic, and idempotents at one vertex are orthogonal. So all
the `O_w(ε)` commute. Every `O_i(g; e)` equals `O_(g v_i)(g e)`, so all the `O_i(g; e)` commute, and hence
so do all the `E_c(g)`. So `X_T` is `D`-quantum rigid for every `D ≥ D_0` and every field `k`, with no
restriction on characteristic or dimension. ∎

## §5. Dynamics (item 3)

- **Minimality.** Suppose `T` has more than two ends, the action is minimal, and no end is fixed.
  - `Λ` fixes no vertex (a fixed vertex would be an invariant subtree). It fixes no end, and it preserves
    no line (a line would be an invariant proper subtree, since `T` has more than two ends).
  - So the action is of general type. Every orbit in `∂T` is dense, and `∂T` has no isolated point
    (Tits; standard, recalled, not re-read).
  - So `X_T ≅ ∂T` is a minimal Cantor system.
- **Topological freeness ⟺ strong faithfulness.** Shadows `∂H` of half-trees `H` form a base of `∂T`.
  - *(⇐)* Suppose `g ≠ 1` fixes an open set of ends, hence some `∂H` pointwise.
    - `∂H` is infinite and has no isolated point. So the union of the geodesics between points of `∂H`
      contains a half-tree `H' ⊆ H`. Take the first vertex `u` of `H` at which two directions lead into
      `∂H`, and let `H'` be one forward branch at `u`. Since `T` is leafless, every vertex of `H'` lies
      on a ray from `u` into `∂H'`, hence on a geodesic between two points of `∂H`.
    - `g` fixes at least three ends, so it is elliptic (a hyperbolic automorphism fixes exactly two). An
      elliptic automorphism fixing two ends fixes the geodesic between them pointwise.
    - So `g` fixes `H'` pointwise, and the action is not strongly faithful.
  - *(⇒)* If `g ≠ 1` fixes a half-tree pointwise, it fixes an open set of ends.
  - For locally finite leafless trees, the pieces of Bux–Llosa Isenrich–Wu are exactly the unions of
    finitely many half-trees, which gives their notion.
- **Isotropy.** Point stabilizers of `X_T` are end stabilizers. So isotropy is torsion-free iff no
  nontrivial element of finite order fixes an end.

## §6. Limits (item 4)

- **Vertex stabilizers.** Topological freeness implies that `Λ` acts faithfully on `∂T`, hence on `T`.
  - `Aut(T)_v` is the inverse limit of the finite groups `Aut(B_n(v))`, because `T` is locally finite.
  - `Stab(v) → Aut(T)_v` is injective. So every nontrivial `k ∈ Stab(v)` acts nontrivially on some finite
    ball, and that ball's automorphism group is a finite quotient separating `k`.
- **(FA) subgroups.** A subgroup with (FA) fixes a vertex of `T`, by definition of (FA). So it lies in a
  vertex stabilizer and is residually finite.
- **Simple (FA) groups.** If it also has no nontrivial finite quotient, it is trivial. ∎

## §7. Baumslag–Solitar groups (Instance 1)

**The tree.** `Λ = BS(m,n) = ⟨a, t | t a^m t^(-1) = a^n⟩` with `|m|, |n| ≥ 2`, `A = ⟨a⟩`, `C = ⟨a^m⟩`. The
Bass–Serre tree has vertices `Λ/A` and edges `Λ/C`, and the edge `gC` joins `gA` to `g t^(-1) A`.
- At the vertex `A` there are two families of edges:
  - **type 1:** `a^i C`, with `i mod m`, to `a^i t^(-1) A`;
  - **type 2:** `a^i t C`, with `i mod n`, to `a^i t A`.
- `a^j` fixes the type-1 edges iff `m | j`. It fixes the type-2 edges iff `a^j ∈ t C t^(-1) = ⟨a^n⟩`,
  i.e. `n | j`.
- **Rescaling.** Crossing the type-1 edge from `A` to `t^(-1) A`: the new stabilizer is `⟨b⟩` with
  `b = t^(-1) a t`, and `a^(mk) = b^(nk)`. So the exponent of a fixing element changes from `j` to
  `jn/m`. Crossing a type-2 edge changes it from `j` to `jm/n`.
- **Arrival type.** An edge of type 1 at one endpoint is of type 2 at the other. So after crossing a
  type-`σ` edge, all type-`σ` edges at the new vertex point forward.
- **Pure paths exist.** Every half-tree contains arbitrarily long type-1-only and type-2-only forward
  paths, because both types have forward edges at its root when `|m|, |n| ≥ 2`.

**Strong faithfulness when `|m| ≠ |n|`.** Suppose `g ≠ 1` fixes a half-tree `H` pointwise.
- `g` fixes the root of `H`, so `g = h a^j h^(-1)` for some `h` and some `j ≠ 0`. Translate by `h^(-1)`.
- Pick a prime `p` with `v_p(m) ≠ v_p(n)`, which exists since `|m| ≠ |n|`. Say `v_p(m) > v_p(n)`; the
  other case uses type 2.
- Along a type-1-only path in `H`, fixing the next edge needs `m` to divide the current exponent. Each
  crossing lowers `v_p` of the exponent by `v_p(m) − v_p(n) ≥ 1`.
- So some edge of the path is moved. This is a contradiction.

**The other hypotheses.**
- Hyperbolic elements fix no vertex.
- The action is minimal, since there is one vertex orbit and a reduced splitting.
- `Λ` fixes no end. The kernel of the Busemann character on an end stabilizer is an increasing union of
  cyclic vertex stabilizers, so end stabilizers are abelian-by-cyclic. But `BS(m,n)` contains a free
  group of rank 2 for `|m|, |n| ≥ 2` (standard, recalled).
- `BS(m,n)` is torsion-free and finitely presented.
- Here `r = 1`, `K_1 = {a}`, and the one edge rule relates `g` and `gt`. So `D_0 = 1`.

## §8. `PSL_2(Z[1/p])` (Instance 3)

- **The tree.** `SL_2(Z[1/p]) = SL_2(Z) ∗_(Γ_0(p)) SL_2(Z)`, with the second factor embedded by
  conjugation by `diag(p, 1)`. It acts on the `(p+1)`-regular Bruhat–Tits tree of `SL_2(Q_p)`,
  type-preservingly, with an edge as quotient (Serre, *Trees*, II.1.4; recalled). Pass to `PSL_2`.
- **Hypotheses of the target.** The vertex stabilizers are copies of `PSL_2(Z)`, which are finitely
  generated. The splitting has proper inclusions of index `p + 1 ≥ 3` on both sides, so the action is
  minimal of general type.
- **Topological freeness.** `∂T = P^1(Q_p)`, and `PSL_2(Q_p)` acts by Möbius maps, which fix at most two
  points unless trivial.
- **Torsion.** An element of order `N` in `PSL_2(Z[1/p])` lifts to `SL_2(Z[1/p])` with eigenvalues
  `ζ, ζ^(-1)`, where `ζ` is a root of unity. Its trace is an algebraic integer in `Z[1/p]`, so it lies in
  `Z ∩ [−2, 2]`. So `N ∈ {1, 2, 3}`.
  - An element fixes a point of `P^1(Q_p)` iff its eigenvalues lie in `Q_p`: `i` for `N = 2`, a primitive
    cube root of unity for `N = 3`.
  - `i ∈ Q_p` iff `p ≡ 1 mod 4`, and `ζ_3 ∈ Q_p` iff `p ≡ 1 mod 3`. Neither holds for `p = 2` or `3`.
  - So the isotropy is torsion-free iff `p = 2`, `p = 3` or `p ≡ 11 mod 12`.
