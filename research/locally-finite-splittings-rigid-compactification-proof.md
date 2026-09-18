---
rg: 2
id: locally-finite-splittings-rigid-compactification-proof
kind: route
title: Label each element by the tree edge that leads its vertex coset toward a unique sink coset of type A, run A's compactification on the sink, and get rigidity from exact transport, edge exclusivity and monotone chains
target: locally-finite-splittings-preserve-rigid-sft-compactifications
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
---

Notation is that of the target.
- **Idempotent order.** For idempotents, `P ≤ Q` means `PQ = QP = P`. It is transitive: if `P ≤ Q ≤ R`, then
  `PR = PQR = PQ = P` and `RP = RQP = QP = P`.
- **Comparable idempotents commute.** Orthogonal ones (`PQ = QP = 0`) satisfy `P ≤ 1 − Q`.

## 1. The tree and the labels

**Tree conventions.**
- Vertices of `T` are cosets `gV_u` of vertex groups. Each element `g ∈ Λ` lies in exactly one vertex coset of each
  type.
- Fix a spanning tree and the usual generators: those of each `V_u`, plus one stable letter `t_ε` for each oriented
  edge `ε` of `𝔾` outside it.
- The edges of `T` at the vertex `hV_u` correspond to the pairs `(ε, cC_ε)`, with `ε` an edge of `𝔾` at `u` and
  `cC_ε ∈ V_u/C_ε`. The pair `(ε, cC_ε)` is the edge to the vertex containing `h c t_ε`.
- Choose once and for all a finite transversal of each `V_u/C_ε`, possible since the index is finite.

**Alphabet.** At an element `h` of vertex type `u` (for its `u`-coset; do this for every `u`, as a product of
coordinates), the label is:
- a pointer `(ε, cC_ε)`, a finite set; or
- if `u = a`, the type of `A`, a letter of `Y_A`, meaning "this coset is the sink".

**Rules** (all local):
- (T) **Transport.** For each generator `b` of `V_u`, `x(hb) = b^(-1)·x(h)` on pointers. Here `V_u` acts on
  `V_u/C_ε` on the left. For `u = a`, the label at `h` is a `Y_A`-letter iff the label at `hb` is.
- (Y) **Sink.** On `Y_A`-letters, `g ↦ x(hg)` (`g ∈ A`) satisfies the forbidden patterns of `Y_A`.
- (X) **Exclusivity.** For each edge `(ε, c)` with `c` in the transversal: `x(h) = (ε, cC_ε)` holds iff the
  label at `h c t_ε` is *not* the pointer back to `hV_u`.

Let `Y` be the resulting SFT, with seed the pattern of `π_A` at the identity, read in `Y_A`-letters.

## 2. Structure: (C1) and (C2)

**Orientation.**
- By (T), a pointer is one edge of `T` at the vertex, independent of the element read. By (X), every edge of `T`
  is oriented, from the endpoint that points along it.
- Every vertex then has out-degree 1, except sink cosets, which have out-degree 0.
- In a tree with all out-degrees `≤ 1` there is at most one sink. Along the path between two sinks the arrows are
  forced toward the first sink, which contradicts the second. The same argument excludes a bi-infinite path
  pointing toward both ends.
- So every `x ∈ Y` has either a unique sink coset (of type `a`, carrying a point of `Y_A`), or an end of `T` to
  which all out-paths converge. Every such datum occurs: point each vertex along its geodesic toward the sink or
  end.

**(C1).**
- The seed forces the `a`-coset of `1` to be the sink, with the configuration `y_(A*)` on it, by (C1) for `Y_A`.
- All pointers are then forced, which gives one point `y_*`.
- If `g.y_* = y_*`, then `g` fixes the sink vertex `A`, so `g ∈ A`, and `g` fixes `y_(A*)`, so `g = 1`.

**(C2).**
- **A sink with a seedless configuration.** Such a point is a limit of `a_n.y_*` with `a_n ∈ A`, by (C2) for `Y_A`.
  Elements of `A` fix the sink vertex, hence preserve every pointer toward it.
- **An end.** Such a point is a limit of `g_n.y_*` with sinks `g_nA` converging to that end in `T`. The pointers on
  any finite subtree agree once the sink lies beyond it.

## 3. Operator lemmas

Let `(E_ℓ(h))` be a `D`-family for `Y`, with `D` at least the radius of the rules and the rigidity scale of `Y_A`.

**(L0)** If a pattern on a set `F` of diameter `≤ 2D` never occurs in `Y`, the product of its site idempotents is
`0`. To see this, sum over extensions to a `D`-ball using Q1: those factors commute (Q2), and each extended
product vanishes by Q3.

**(L1) Exact transport.** Suppose (T) or (X) says: label `ℓ` at `h` iff label `ℓ'` at `h'`.
- Then `E_ℓ(h)(1 − E_ℓ'(h')) = 0` and `(1 − E_ℓ(h))E_ℓ'(h') = 0`, by (L0).
- So `E_ℓ(h) = E_ℓ(h)E_ℓ'(h') = E_ℓ'(h')`.
- **Consequences.**
  - For each vertex `v` and each edge `f` at `v`, the operator `Π_v(f)` ("`v` points along `f`") is the same
    whichever element of `v` it is read at.
  - So is `Σ_v` ("`v` is the sink"), the sum of the `Y_A`-letter idempotents at any element of `v`.
  - The operators `{Π_v(f)}_f ∪ {Σ_v}` are pairwise orthogonal idempotents summing to `1`, since they are the
    labels at one site.

**(L2) Edge exclusivity.** For the edge `f = vw`: `Π_v(f) + Π_w(f) = 1`.
- By (X) and (L0): `Π_v(f)Π_w(f) = 0` and `(1 − Π_v(f))(1 − Π_w(f)) = 0`. Here the two sites are at bounded
  distance, so the factors commute.
- Expanding the second equation gives `Π_v(f) + Π_w(f) = 1`.

**(L3) Monotone chain.** Let `v = v_0, v_1, …, v_m = w` be a tree path with edges `f_i = v_(i−1)v_i`. Then
`1 − Π_v(f_1) ≤ Π_w(f_m)`.
- For `i < m`: `Π_(v_i)(f_i) ≤ 1 − Π_(v_i)(f_(i+1))`, by orthogonality in (L1).
- And `1 − Π_(v_i)(f_(i+1)) = Π_(v_(i+1))(f_(i+1))`, by (L2).
- Start from `1 − Π_v(f_1) = Π_(v_1)(f_1)`, also by (L2), and chain by transitivity.

**(L4) Domination.** Suppose `P ≤ Q` for `Q` in the partition `𝒫_w = {Π_w(f)}_f ∪ {Σ_w}`. Then `P`, and hence
`1 − P`, commutes with every member of `𝒫_w`, and with every idempotent `R ≤ Q'` for some `Q' ∈ 𝒫_w`, `Q' ≠ Q`.
- `P` commutes with `Q` because `P ≤ Q`.
- For `Q' ≠ Q`: `PQ' = PQQ' = 0 = Q'QP = Q'P`.
- Then `PR = (PQ')R = 0` and `RP = R(Q'P) = 0`.

## 4. Rigidity

**Same coset `v`.**
- The pointer operators are the fixed operators `Π_v(f)`, and they commute (L1).
- If `v` has type `a`, put `F_ℓ(g) = E_ℓ(hg) + (1 − Σ_v)·[z(g) = ℓ]` for `g ∈ A`, with `z ∈ Y_A` fixed and `ℓ` a
  `Y_A`-letter.
  - `F` is a partition of unity on each site, since `Σ_v` is the sum of the `E_ℓ(hg)` there.
  - It commutes at `A`-distance `≤ 2D`, because `d_Λ ≤ d_A` on a coset.
  - It kills every pattern on an `A`-ball of radius `D` not occurring in `Y_A`: on the `Σ_v` part by (L0),
    since on a sink coset `Y` restricts to `Y_A`; and trivially on the `z` part.
  - So `F` is a `D`-family for `Y_A`, hence commutative. The operators `E_ℓ(hg) = Σ_v F_ℓ(g)` therefore commute
    with each other and with `Σ_v`.
  - They are orthogonal to the pointers, which lie below `1 − Σ_v`.

**Different cosets `v ≠ w`.** Take the tree path as in (L3). Every label idempotent at an element of `v` is one of:
- `Π_v(f)` with `f ≠ f_1`, which is `≤ 1 − Π_v(f_1)`;
- `Σ_v` or a sink letter `≤ Σ_v`, which is `≤ 1 − Π_v(f_1)`;
- `Π_v(f_1) = 1 − (1 − Π_v(f_1))`.

In each case it is, or is `1` minus, an idempotent `≤ 1 − Π_v(f_1) ≤ Π_w(f_m)` (L3). Every label idempotent at an
element of `w` is a member of `𝒫_w` or lies below `Σ_w ≠ Π_w(f_m)`. By (L4) they commute.

**Assembling.**
- A site idempotent is a product of coordinate idempotents at its site, one coordinate per vertex type. These
  commute by Q1.
- Two coordinates are either at the same site or at elements of vertices `v, w`. The second case is covered by one
  of the two cases above, including `v = w`.

So all site idempotents commute, and `Y` is `D`-quantum rigid. ∎

## 5. Remarks

- **Where rigidity comes from.** The only rigidity input is `Y_A` on the sink coset. The tree part is rigid at
  every scale by (L1)–(L4), with no hypothesis on the other vertex groups. This is why they may be arbitrary.
- **Why local finiteness.** It is used exactly once: to make the pointer alphabet finite. With an infinite-index
  edge group, a pointer must name a coset `cC_ε` in an infinite set. Tree gluing handles `C_ε = 1` with seeds; the
  general case needs a relative seed, an SFT on `V_u` whose seed-forced point has stabilizer `C_ε`.
