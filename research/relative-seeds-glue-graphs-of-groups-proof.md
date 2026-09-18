---
rg: 2
id: relative-seeds-glue-graphs-of-groups-proof
kind: route
title: Give each vertex coset a type and a relative-seed configuration whose seed coset is its exit, orient the Bass–Serre tree by exclusivity, and get rigidity from atoms, monotone chains and domination
target: relative-seeds-glue-graphs-of-groups-into-class-c
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
  - locally-finite-splittings-preserve-rigid-sft-compactifications
---

Notation is that of the target. As in `locally-finite-splittings-rigid-compactification-proof`, `P ≤ Q` means
`PQ = QP = P`, and this order is transitive. That proof's lemma (L0) is used unchanged: a pattern of diameter `≤ 2D`
that never occurs has vanishing product.

## 1. Gluing: the SFT

**Tree conventions.**
- Vertices of `T` are cosets `hV_u`.
- The edges at `hV_u` are the pairs `(ε, aC_ε)`, with `o(ε) = u` and `a ∈ V_u`. The pair `(ε, aC_ε)` joins
  `hV_u` to the vertex containing `h a t_ε`, where `t_ε = 1` on a spanning tree.
- The reverse edge at `h a t_ε` is `(ε̄, C_(ε̄))`.

**Data.** For each oriented edge `ε`, fix a rigid relative seed `(Y_ε, π_ε)` for `(V_(o(ε)), C_ε)`. For the chosen
vertex `u_0`, fix a rigid relative seed `(Y_0, π_0)` for `(V_(u_0), C)`.

**Coordinates.** Each element `h` carries one coordinate for each vertex type `u`, describing its `u`-coset `v`:
- a *type* `τ ∈ {ε : o(ε) = u}`, together with `u = u_0` ⇒ also the type `0`;
- a letter of `Y_τ`.

**Rules.**
- (T) **Type transport.** The type is constant along generators of `V_u`.
- (Y) **Configuration.** On a coset of type `τ`, `g ↦ x(hg)` (`g ∈ V_u`) obeys the forbidden patterns of `Y_τ`.
- (X) **Exclusivity.** For each `ε` and each `h`, exactly one of the following holds:
  - the `u`-coordinate at `h` has type `ε` and `π_ε` occurs at `h`;
  - the `u'`-coordinate at `h t_ε` has type `ε̄` and `π_(ε̄)` occurs at `h t_ε`.

**Structure.**
- **Out-degree.** Say `v` *points along* `(ε, aC_ε)` if `v` has type `ε` and its configuration has seeds on `aC_ε`.
  A point of `Y_ε` with a seed at `a` equals `a.y_*^ε`, by (RS1). So its seeds form exactly the coset `aC_ε`, and
  every vertex has out-degree `≤ 1`.
- **Orientation.** By (X), each tree edge is pointed along by exactly one endpoint. Exactly as in tree gluing, a
  point has a unique sink or a unique end. A sink is a vertex of type `0`, or a vertex whose `Y_ε`-configuration is
  seedless.
- **(RS1).** The seed "`u_0`-coordinate of type `0` with `π_0` at `1`" makes the `u_0`-coset `V_(u_0)` a sink
  carrying `y_*^0`. All pointers are then forced, and each non-sink vertex carries `a.y_*^ε` for its exit coset
  `aC_ε`. So the cylinder is one point `y_*`, and `Stab(y_*) = Stab_(V_(u_0))(y_*^0) = C`.
- **(RS2).** There are four kinds of point, each a limit of translates of `y_*`.
  - A type-`0` sink with any `Y_0`-configuration: by (RS2) for `Y_0`, since elements of `V_(u_0)` fix the sink
    vertex and every pointer toward it.
  - A type-`ε` sink with a seedless configuration `z = lim a_n.y_*^ε`: here `a_nC_ε -> ∞`. Place the true sink
    beyond the edge `a_nC_ε`. A finite subtree around the origin eventually misses that edge, so it sees `v` as
    its sink, with configuration `a_n.y_*^ε -> z`.
  - An end: move the sink toward it.
  - A translate of `y_*`.

## 2. Gluing: rigidity

Let `(E)` be a `D`-family, with `D` at least the rule radius and the rigidity scales of all `Y_τ`.

**(A) Each coset is commutative, with atoms.** Fix a vertex `v` of type coordinate `u`.
- **Type indicators.** `T_v(τ)` is the sum of the type-`τ` letters at any element of `v`. It is the same operator
  at all elements, by (T) and the transport step (L1) of the locally finite proof. So it commutes with every letter
  at every element of `v`.
- **Commutativity.** For each `τ`, put `F_ℓ(g) = E_ℓ(hg)T_v(τ) + (1 − T_v(τ))[z(g) = ℓ]` with `z ∈ Y_τ`. This is a
  `D`-family for `Y_τ` on `V_u`:
  - `d_Λ ≤ d_(V_u)` on the coset;
  - illegal `V_u`-patterns of type `τ` are illegal in `Y`, by (Y) and (L0).
  - Hence `F` is commutative. Its idempotents define a unital homomorphism `ψ_(v,τ) : LC(Y_τ) -> End(W)`, since
    a commutative family obeying the defining patterns realizes the clopen algebra.
- **The algebra.** So the letters at `v` generate the commutative algebra
  `𝒜_v = Σ_τ T_v(τ) ψ_(v,τ)(LC(Y_τ))`.
- **Atoms.** For an edge `f = (ε, aC_ε)` put `Π_v(f) = T_v(ε) ψ_(v,ε)([π_ε at a])`. This is the local
  "type `ε` and seed at `a`" idempotent.
  - The clopen `[π_ε at a]` is the single point `{a.y_*^ε}`, and it equals `[π_ε at ac]` for `c ∈ C_ε`. So
    `Π_v(f)` does not depend on the representative.
  - For every idempotent `X ∈ 𝒜_v` it is an **atom**: `XΠ_v(f) = Π_v(f)X ∈ {0, Π_v(f)}`.
  - Distinct edges at `v` give orthogonal atoms: different types, or disjoint singletons.

**(B) Exclusivity.** For the edge `f = vw`: `Π_v(f) + Π_w(f) = 1`. Apply (L0) to (X): both factors are local
pattern idempotents at bounded distance, so they commute.

**(C) Monotone chain.** For a tree path `v = v_0, …, v_m = w` with edges `f_i`: `1 − Π_v(f_1) ≤ Π_w(f_m)`.
- (B) gives `1 − Π_(v_i)(f_(i+1)) = Π_(v_(i+1))(f_(i+1))`.
- Orthogonality in (A) gives `Π_(v_i)(f_i) ≤ 1 − Π_(v_i)(f_(i+1))`.
- Chain these by transitivity.

**(D) Domination.** Let `Q` be an atom of `𝒜_w`, so `YQ = QY = ε_Y Q` with `ε_Y ∈ {0, 1}` for idempotents `Y` of
`𝒜_w`. If `P ≤ Q`, then `PY = PQY = ε_Y P` and `YP = YQP = ε_Y P`. So `P` commutes with all of `𝒜_w`.

**Different cosets `v ≠ w`.** Let `X` be a letter idempotent at an element of `v`. It commutes with `Π_v(f_1)` by (A),
so `X = XΠ_v(f_1) + X(1 − Π_v(f_1))`.
- `XΠ_v(f_1) ∈ {0, Π_v(f_1)}`, and `Π_v(f_1) = 1 − (1 − Π_v(f_1))`.
- `X(1 − Π_v(f_1)) ≤ 1 − Π_v(f_1) ≤ Π_w(f_m)`, by (C).

By (D), both pieces, and hence `X`, commute with every letter at `w`.

**Conclusion.** Letters at one coset commute by (A), and coordinates at one site commute by Q1. So every site
idempotent, being a product of coordinate letters, commutes with every other. So `Y` is `D`-quantum rigid. ∎

**Remark.** The only rigidity input is the family `Y_τ` on each coset.
- **Along the tree, rigidity is free.** It comes from exclusivity, from the atoms, which exist because each seed
  cylinder is a single point, and from monotone chains.
- **The two earlier cases.**
  - With `C_ε = 1` this is tree gluing.
  - With `[V : C_ε] < ∞`, `Y_ε` is the finite shift on `V/C_ε`. Its atoms are the pointer labels of
    `locally-finite-splittings-rigid-compactification-proof`.

## 3. Induction

Let `C ≤ H ≤ A` with `[A:H] < ∞` and `(Y_H, π_H)` for `(H, C)`.

**The SFT over `A`.** Its alphabet is `(A/H) × (Σ ⊔ {□})`, where `A/H` is the set of left cosets.
- (I1) The `A/H`-coordinate `λ` satisfies `λ(gs) = s^(-1)λ(g)` for generators `s`. So `λ(g) = g^(-1)M` for one
  left coset `M`, the *marked* coset.
- (I2) The `Σ`-letter is non-blank iff `λ(g) = H`, i.e. `g ∈ M`.
- (I3) On `M`, `h ↦ x(gh)` obeys `Y_H` (with `g ∈ M`). This uses words for generators of `H`, which is local.

**Properties.**
- The point `z_* = (M = H, y_*)` is isolated, with seed `λ(1) = H` and `π_H`. Its stabilizer is
  `{a : aH = H, a.y_* = y_*} = C`.
- The orbit closure is everything: use translates, and (RS2) for `Y_H`.

**Rigidity.**
- The `λ`-idempotents are exactly transported. So they are the finitely many operators `[M = rH]`, which are one
  partition and are central for the family.
- On `[M = rH]`, the `Σ`-letters of the coset `rH` form, after the F-trick, a family for `Y_H`. The inclusion
  `H -> A` is a quasi-isometry, so take `D` large. That family is commutative.
- `Σ`-letters on different cosets have orthogonal supports, so their products vanish in both orders. ∎

## 4. Membership is consumed

Let the word problem of `A` be solvable. Then the set of locally admissible patterns on each ball `B_m` is
computable.

**Computing `y_*`.** Fix `n`.
- For each `m ≥ n`, list the patterns `p` on `B_n` that agree with `π` on `B_(R_0)` and extend to locally
  admissible patterns on `B_m`.
- By (RS1) and compactness, exactly one `p` survives for all `m`, namely `y_*|_(B_n)`. Every other candidate
  fails at some finite `m`.
- So increase `m` until one candidate remains. This computes `y_*|_(B_n)`.

**Deciding membership.** `g ∈ C` iff `y_*` has a seed at `g`, which reads `y_*` on `g B_(R_0)`. ∎

## 5. Corollaries (a)–(c)

- **(a) Subgroups of free groups.** Let `H = C * D ≤ F_n` be of finite index (M. Hall).
  - Apply §1 to the graph of groups `C — D` with trivial edge group. The edge seeds are seeds of the free groups
    `C, D ∈ 𝒞`. Take `u_0 = C` and `Y_0` the one-point shift. This gives `(H, C) ∈ 𝓡`.
  - Then apply §3.
- **(b) Subgroups of `Z^m`.** In a Smith basis, take the product of finite shifts and copies of `C_Z`.
- **(c) Graphs of free and free abelian groups.** Every vertex group is in `𝒞` (free groups, and `Z^m` via
  products of `C_Z`). Every edge pair is in `𝓡` by (a) and (b). Apply §1 with `C = 1`.

## Referee (bh-ref-engines, 2026-09-18): PASS

See the Referee section of the target node. Small notes:
- (A) should state the convention that the generating set of `Λ` contains those of the vertex groups, so that
  `d_Λ ≤ d_(V_u)`.
- (RS2), end case: the sink can be any `u_0`-vertex within `diam(𝔾)` of a far ray vertex.
