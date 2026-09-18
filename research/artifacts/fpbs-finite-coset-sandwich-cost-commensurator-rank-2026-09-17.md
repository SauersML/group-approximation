# Finite-coset sandwiches cost at least the rank of the commensurator

Worker `swarm-0917-w12-w12-fp-follow`, lane w12-fp-follow, target
`fpbs-free-group-sandwich-cost-is-two` (MC).

## 0. Setup

- `F` is a free group of finite or countable rank. `a` is a free p.m.p.
  action of `F` on a standard probability space `(X, μ)`. Write `gx` for
  `a(g)x`.
- `K ≤ F` is finitely generated and non-trivial. It has rank `r = rk K`.
- `E` is a Borel equivalence relation with `E_{a|K} ⊆ E ⊆ E_a` (a
  *sandwich*).
- Costs `C(·)` of a relation on an invariant Borel set `Z` are
  **unnormalized**: they are computed with `μ|Z`, so `C(E_{a|K}|Z) = r μ(Z)`.
  Where normalized cost is meant, it is written `C_1(·)`.

**Coset field.** For `x ∈ X` put

```text
T(x) = { g ∈ F : (x, gx) ∈ E },     S(x) = K\T(x) ⊆ K\F,     d(x) = |S(x)|.
```

`T(x)` is left `K`-invariant, because `kgx E_{a|K} gx E x`. So `S(x)` is a
set of right cosets `Kh`. By freeness `g ↦ gx` is a bijection from `T(x)`
onto `[x]_E`. The `K`-orbits in `[x]_E` are the sets `Khx` for `Kh ∈ S(x)`.
So `d(x)` is the number of `K`-orbits in the `E`-class of `x`. Put

```text
Y_d = { x : d(x) = d }  (1 ≤ d < ∞),   Y_fin = ⋃_d Y_d,   Y_∞ = { d = ∞ }.
```

**Lemma 0 (transformation rules).**
1. `T(gx) = T(x) g^{-1}` for `g ∈ T(x)`.
2. In particular, `S(kx) = S(x)·k^{-1}` for `k ∈ K`.
3. `d` is `E`-invariant, and all the sets above are Borel and
   `E`-invariant.

*Proof.* If `g ∈ T(x)` then `gx E x`. So `g'gx E gx` iff `g'g ∈ T(x)`,
which gives `T(gx) = T(x)g^{-1}`. Right multiplication by `g^{-1}` permutes
the right `K`-cosets, so `d(gx) = d(x)`. For Borel measurability,
`{x : Kh ∈ S(x)} = {x : (x, hx) ∈ E}` is Borel for every `h`, and `F` is
countable. ∎

## 1. The commensurator of a finitely generated subgroup

Let `𝒯` be the Cayley tree of `F` for a free basis, with `F` acting on the
left. This action is free on vertices and has no inversions. So every
`1 ≠ g ∈ F` is hyperbolic, with an axis `A_g`: a bi-infinite line on which
`g` translates. Put

```text
T_K = ⋃_{1 ≠ k ∈ K} A_k,        M = { h ∈ F : h T_K = T_K }.
```

Standard facts:
- (a) `A_{g^n} = A_g` for `n ≠ 0`.
- (b) `A_{hgh^{-1}} = h A_g`.

**Lemma 1.**
1. `K ≤ M`, and `[M : K]` is at most the number of `K`-orbits of vertices
   of `T_K`, which is finite.
2. `M = Comm_F(K)`.
3. If `K` is non-cyclic, then `M` is free of finite rank with
   `rk M − 1 = (rk K − 1)/[M:K]`. In particular `rk M ≥ 2`.

*Proof.* **(1)** By (b), `k T_K = T_{kKk^{-1}} = T_K` for `k ∈ K`, so
`K ≤ M`.

Fix a vertex `v_0` and generators `k_1, …, k_r` of `K`. Put
`P = ⋃_i [v_0, k_i v_0]`. The set `U = ⋃_{k∈K} kP` is connected, because
`kP ∋ kk_i v_0 ∈ kk_i P`. So `U` is a subtree. It has finitely many
`K`-orbits of vertices, at most the number of vertices of `P`.

`T_K ⊆ U`. For `k ≠ 1`, the geodesic `[k^{-n}v_0, k^n v_0]` lies in `U`,
since it lies in any subtree containing both ends. It contains the segment
of `A_k` between the projections of its endpoints, and these segments
exhaust `A_k` as `n → ∞`.

So `T_K` has finitely many `K`-orbits of vertices, and at least one vertex.
`M` acts freely on the vertices of `T_K`. Each `M`-orbit of vertices is
therefore a union of exactly `[M:K]` distinct `K`-orbits, and `[M:K]` is
finite.

**(2)** Let `h ∈ Comm_F(K)`, and put `L = K ∩ hKh^{-1}`. It has finite
index in `K` and in `hKh^{-1}`. For a subgroup `L ≤ G` of finite index,
`T_L = T_G`. Indeed `T_L ⊆ T_G` trivially, and each `1 ≠ g ∈ G` has some
`g^n ∈ L` with `n ≠ 0`, so `A_g = A_{g^n} ⊆ T_L` by (a). Hence

```text
T_K = T_L = T_{hKh^{-1}} = h T_K
```

by (b), so `h ∈ M`.

Conversely, `[M:K] < ∞` by (1). For `h ∈ M`, the subgroups `K` and
`hKh^{-1}` both have finite index in `M`. So their intersection has finite
index in each of them, and `h ∈ Comm_F(K)`.

**(3)** `M` is a subgroup of a free group, hence free. It contains `K` with
finite index, so the Schreier index formula gives
`rk M − 1 = (rk K − 1)/[M:K]`. The right side is positive when
`rk K ≥ 2`, and `rk M − 1` is an integer, so `rk M ≥ 2`. ∎

*Remark.* Lemma 1 is the classical fact that a finitely generated subgroup
of a free group has finite index in its commensurator. It is proved here
from scratch so that nothing further needs importing. The bound
`[M:K] ≤ #(K\V(T_K))` is effective: for `K = ⟨a, bab^{-2}⟩ ≤ F_2`, the
graph `K\T_K` is the core of the Stallings graph, with 3 vertices.

## 2. On the finite part, every class lies in one `Comm(K)`-orbit

**Lemma 2.** For `μ`-a.e. `x ∈ Y_fin`, `T(x) ⊆ M = Comm_F(K)`. Hence:
- `S(x) ⊆ K\M`;
- `d(x) ≤ [M:K]`, so `Y_d` is null for `d > [M:K]`;
- `E|Y_fin ⊆ E_{a|M}` up to a null set.

*Proof.* **Step 1 (invariant measure on a countable set).** Let `𝒫` be the
countable set of finite subsets of `K\F`. `K` acts on it by
`k·Σ = Σ k^{-1}`. By Lemma 0 the map `S : Y_fin → 𝒫` is Borel and
`K`-equivariant, and `Y_fin` is `K`-invariant. So `ν = S_*(μ|Y_fin)` is a
finite `K`-invariant measure on the countable set `𝒫`.

Each atom of `ν` therefore has a finite `K`-orbit. An infinite orbit of an
atom of mass `c > 0` would carry mass `∞ · c`.

So for a.e. `x ∈ Y_fin`, the finite set `S(x)` has a finite `K`-orbit. Its
stabilizer then has finite index, and so does the kernel of the stabilizer's
action on the finite set `S(x)`. Hence every `Kh ∈ S(x)` has a finite
`K`-orbit. The stabilizer of `Kh` is
`{k : hk^{-1}h^{-1} ∈ K} = K ∩ h^{-1}Kh`. So

```text
[K : K ∩ h^{-1} K h] < ∞       for every Kh ∈ S(x).            (2.1)
```

**Step 2 (symmetrize).** Let `G ⊆ Y_fin` be the conull set where (2.1)
holds. `F` is countable and preserves `μ`, so the set
`Z = X ∖ F·(Y_fin ∖ G)` is conull and `F`-invariant.

Let `x ∈ Y_fin ∩ Z` and `Kh ∈ S(x)`. Put `y = hx`. Then `y ∈ [x]_E`, so
`y ∈ Y_fin` because `Y_fin` is `E`-invariant, and `y ∈ Z`. So `y ∈ G`.

Also `h^{-1} y = x ∈ [y]_E`, so `Kh^{-1} ∈ S(y)`. Applying (2.1) at `y`
gives `[K : K ∩ hKh^{-1}] < ∞`. Conjugating by `h^{-1}` turns this into
`[h^{-1}Kh : h^{-1}Kh ∩ K] < ∞`.

Together with (2.1), `h ∈ Comm_F(K) = M` (Lemma 1). ∎

Lemma 2 extends Lemma 5 of
`research/artifacts/fpbs-sandwich-cost-fiber-formula-2026-09-17.md`. That
lemma is the conjugation-invariant version of Step 1. Here the invariant
measure lives on finite sets of cosets.

## 3. A finite-coset piece costs at least `1 + (rk K − 1)/d`

**Lemma 3.** Let `1 ≤ d < ∞` with `μ(Y_d) > 0`. Then, for normalized cost,

```text
C_1(E|Y_d) ≥ 1 + (rk K − 1)/d.
```

Lemma 3 does not use Lemma 2 or any hypothesis on `K` beyond finite
generation.

*Proof.* **The covering relation.** Put

```text
Ŷ = { (x, Kh) : x ∈ Y_d,  Kh ∈ S(x) } ⊆ Y_d × K\F,
```

with `ν = μ × (counting)`. Then `ν(Ŷ) = d μ(Y_d)`. The point `(x, Kh)`
stands for "`x` together with the `K`-orbit `Khx ⊆ [x]_E`".

Define `Ê` on `Ŷ` by

```text
(x, Kh) Ê (x', Kh')  ⟺  x E x'  and  Khx = Kh'x'.
```

For `g ∈ F`, the Borel bijection

```text
θ_g(x, Kh) = (gx, Khg^{-1}),   on  { (x, Kh) ∈ Ŷ : gx E x },
```

lands in `Ŷ`. By Lemma 0, `hg^{-1}` lies in `T(gx)`, and
`Khg^{-1}·gx = Khx`. So `θ_g` preserves `ν`.

The maps `θ_g` generate `Ê`. If `(x,Kh) Ê (x',Kh')`, write `x' = gx` with
`g ∈ T(x)`. Then `Kh'gx = Khx`, so `Kh' = Khg^{-1}` by freeness. So `Ê` is
a p.m.p. countable Borel equivalence relation on `(Ŷ, ν)`. The projection
`(x, Kh) ↦ x` maps each `Ê`-class bijectively onto an `E`-class.

**Lifting graphings.** Let `Φ = (φ_i : D_i → R_i)` be a graphing of
`E|Y_d`. Partition each `D_i` into Borel pieces on which `φ_i(x) = g x` for
a fixed `g`. On the piece for `g`, set
`φ̂_i(x, Kh) = θ_g(x, Kh) = (gx, Khg^{-1})`, with domain the set of
`(x, Kh) ∈ Ŷ` such that `x` lies in that piece. Then:
- `ν(dom φ̂_i) = d μ(D_i)`.
- A `Φ`-path `x = x_0, …, x_n = x'` lifts, from any `(x, Kh)`, to a
  `Φ̂`-path ending at `(x', Kh')` with `Kh'x' = Khx`. So `Φ̂` generates
  `Ê`.

Normalizing by `ν(Ŷ) = d μ(Y_d)` and `μ(Y_d)` gives
`C_1(Ê) ≤ C_1(Φ)`, and so

```text
C_1(Ê) ≤ C_1(E|Y_d).                                           (3.1)
```

**The complete section.** Put `A = { (x, Kh) ∈ Ŷ : Kh = K }`, i.e. the pairs
of `x` with its own `K`-orbit. Then:
- `ν(A) = μ(Y_d)`, which is `1/d` of `ν(Ŷ)`.
- `A` is a complete section of `Ê`: `(x, Kh)` is `Ê`-equivalent to
  `θ_h(x, Kh) = (hx, K) ∈ A`.
- `(x, K) Ê (x', K)` iff `x E x'` and `Kx = Kx'`, i.e. iff
  `x' ∈ Kx`. So `(x, K) ↦ x` is a measure-preserving isomorphism of
  `(A, Ê|A)` onto `(Y_d, E_{a|K}|Y_d)`.

The action of `K` on `Y_d` (normalized) is free and p.m.p. A free basis
`k_1, …, k_r` of `K` is therefore a treeing of `E_{a|K}|Y_d`: a cycle
would give a non-trivial reduced word fixing a point. By
`gaboriau-treeable-free-action-realizes-min-cost` (1), treeings compute
cost, so

```text
C_1(Ê|A) = C_1(E_{a|K}|Y_d) = r.
```

By `gaboriau-induction-formula-complete-section`, with normalized measure
`1/d` for `A`,

```text
C_1(Ê) − 1 = (1/d)(C_1(Ê|A) − 1) = (r − 1)/d.
```

With (3.1) this proves the lemma. ∎

*Remark.* Lemma 3 is the finite-index cost inequality
`C(E) − 1 ≥ (C(E_K) − 1)/[E : E_K]`. It is proved with the constant-index
pieces made explicit, so ergodicity of `E` is never used.

## 4. The theorem

**Theorem.** Let `F` be free, `a` a free p.m.p. action of `F`, and
`K ≤ F` finitely generated and non-cyclic. Put `M = Comm_F(K)`. For every
sandwich `E_{a|K} ⊆ E ⊆ E_a`:

1. `[M:K] < ∞`. A.e. `E`-class in `Y_fin` is a union of at most `[M:K]`
   `K`-orbits, all inside one `M`-orbit, so `E|Y_fin ⊆ E_{a|M}`.
2. `C(E|Y_fin) ≥ rk(M)·μ(Y_fin) ≥ 2 μ(Y_fin)`. This is sharp: `E = E_{a|M}`
   has `Y_fin = X` and cost `rk M`.
3. If `rk K = 2`, then `M = K` and `E|Y_fin = E_{a|K}|Y_fin`.

*Proof.*
1. Lemmas 1 and 2.
2. The pieces `Y_d` are `E`-invariant, and `Y_d` is null for `d > [M:K]`.
   Cost is additive over a countable partition into `E`-invariant Borel
   sets: a graphing of `E|Y_fin` restricts to a graphing on each piece, and
   the union of graphings on the pieces is a graphing of `E|Y_fin`. So by
   Lemma 3 and Lemma 1(3),

   ```text
   C(E|Y_fin) = Σ_{d ≤ [M:K]} μ(Y_d) C_1(E|Y_d)
             ≥ Σ_d μ(Y_d) (1 + (rk K − 1)/[M:K])
             = rk(M) μ(Y_fin).
   ```

3. `rk M − 1 = 1/[M:K]` is a positive integer, so `[M:K] = 1`. Then (1)
   gives `d = 1` a.e. on `Y_fin`. ∎

**Corollary (reduction of MC).** Take `F = F_2`. For a sandwich `E` write
`Y_∞(E)` for its infinite-coset part. Then

```text
C(E) ≥ 2 μ(Y_fin) + C(E|Y_∞(E)).
```

So `fpbs-free-group-sandwich-cost-is-two` follows from **MC_∞**: every
sandwich satisfies `C(E|Y_∞) ≥ 2 μ(Y_∞)`. Every counterexample to MC has
`μ(Y_∞) > 0`, and its infinite-coset part carries cost density below 2.

## 5. What is killed, and what is left

**Class kill.**
- *Class.* Sandwiches in which, on a positive-measure set, `E`-classes are
  finite unions of `K`-orbits. This includes every finite-index extension
  of `E_{a|K}`. It also includes the mechanism behind the §5 example of the
  fiber-formula artifact, a treeable relation of cost 3/2 containing a free
  `F_2`-relation with index 2.
- *Invariant.* `Comm_F(K)`, with `[Comm_F(K) : K] ≤ #(K\V(T_K))`.
- *Step where every member dies.* Lemma 2, Step 1. The finite measure
  `S_*(μ|Y_fin)` lives on a countable `K`-set, so it lives on finite
  `K`-orbits. That forces `S(x) ⊆ K\Comm(K)`. The covering relation of
  Lemma 3 then prices the extension at `rk Comm(K) ≥ 2`.
- *Contrast with the unconstrained world.* Outside `E_a`, a finite-index
  extension of a free `F_2`-relation can cost `3/2`. Inside `E_a`, the
  finite-index extensions available are exactly those inside
  `E_{a|Comm K}`. For rank-2 `K` there are none.

**Reframing of MC_∞.** A sandwich is the same thing as an `F`-equivariant
Borel map `x ↦ 𝔓(x)` into partitions of `K\F` with blocks
`{Kh : hx E x'}`. The rule `𝔓(gx) = 𝔓(x)g^{-1}` follows from Lemma 0.
The root block is `S(x)`.

On `Y_∞` the root block is infinite. `K\F ∖ K\M` is a countable `K`-set
whose orbits are all infinite, so Step 1 has no analogue there. MC_∞ asks
that every such `F`-invariant random partition into infinite blocks, pulled
back to a free action, has cluster relation of cost at least 2 on `Y_∞`.

The contact example already shows that an infinite-coset merge can land at
cost exactly 2. For `K = ⟨a, bab^{-1}⟩`, adding `b|_A` on any positive-measure
`A` absorbs to `E_a` whenever `⟨a⟩` acts ergodically. The reason is that
`b a^n x = (b a^n b^{-1}) b x`, so `b|_{a^n A} ⊆ E`. So
the open core of MC_∞ is:
- malnormal `K`, for example `⟨a, bab^{-2}⟩`;
- a twisted infinite-coset partition that is not group-generated.

The group-generated case is already covered by
`fpbs-sandwich-cost-fiber-formula` (C).

**Not claimed.** No lower bound on `C(E|Y_∞)` is proved here. A hull
Euler-characteristic heuristic,
`β_1(E) = E_x Σ_{C : x ∈ Hull(C)} (deg_C(x) − 2)/2`, reproduces the
values `rk − 1` on all group-generated sandwiches. Its finiteness
hypotheses on `Y_∞` were not checked, and it is recorded only as a
suggestion.
