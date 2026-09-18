---
rg: 2
id: rover-nekrashevych-vdr-sigma-full-via-type-r-partitions
kind: route
title: Let V_{d,r}(G) act on type-r clopen partitions with at least m+1 blocks; contract the nondirected poset as a directed union of truncated r mod k partition posets
target: rover-nekrashevych-vdr-sigma-full-for-every-r
requires:
  - r-mod-k-partition-posets-truncations-highly-connected
  - one-mod-k-partition-posets-are-highly-connected
  - meinert-cocompact-action-criterion
  - characters-living-on-m-plus-one-factors-lie-in-sigma-m
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Notation is that of the claim.

- Sections satisfy `g(uw) = g(u) g|_u(w)`, `(gh)|_u = g|_{h(u)} h|_u` and `g|_{uv} = (g|_u)|_v`.
- Put `r_0 in {1, ..., k}` with `r_0 ≡ r mod k`, `g_0 = gcd(r_0, k)`, `k' = k/g_0` and `T = {r_0, r_0 + k, ...}`.
- For `d = 2` we have `k = k' = 1`, and every statement below holds with all congruences trivial.

The argument is `rover-nekrashevych-bnsr-full-via-type-one-partitions` with three changes:

- the living-character input (§1), which that route lacked for `r >= 2`;
- contractibility of a nondirected poset (§3, Step 2);
- the modulus `k'` in place of `k` (§3, Step 3).

For self-containedness §2 also reproves, for `C_r`, the parts of `rover-nekrashevych-type-one-clopen-stabilizers-are-copies`
(**Copies**) that are used.

## 0. Local maps

Let `A, B ⊆ C_r` be clopen. A homeomorphism `f: A -> B` is **G-local** if some cone partition `A = ⊔_i C_{α_i}` has
`f(α_i w) = β_i g_i(w)` with `g_i in G`. Every clopen set is a finite union of cones, and any two cone partitions of
`A` have a common refinement, for instance all cones of one large depth inside `A`.

- **(L1) Refinement.** `f(α_i u w) = β_i g_i(u) g_i|_u(w)`. So any finer cone partition of `A` also witnesses
  G-locality, and every row image `f(C_{α_i u}) = C_{β_i g_i(u)}` is a cone.
- **(L2) Inverses and composition.**
  - The `C_{β_i}` partition `B`, and `f^{-1}(β_i w) = α_i g_i^{-1}(w)`.
  - For `f': B -> B'` G-local with rows `(γ_j, δ_j, g'_j)`, refine the rows of `f` (by (L1)) until each `C_{β_i}`
    lies in some `C_{γ_j}`, say `β_i = γ_j z`. Then `f' f(α_i w) = δ_j g'_j(z) (g'_j|_z g_i)(w)`.
- **(L3)** `Γ` is the group of G-local self-homeomorphisms of `C_r`, and `V_{d,r}` is the case `G = 1`.
  - `Γ_A = {h in Γ : h = id off A}`.
  - If `f: A -> A` is G-local, its extension by the identity lies in `Γ_A`, with identity rows on a cone partition of
    `C_r \ A`.
  - Conversely, if `h in Γ` and `h(A) = A`, then `h|_A` is G-local. Refine a table of `h` until `A` is a union of
    domain cones, and keep those rows.

## 1. Characters (item 1 of the claim)

**(C0) Φ_χ.** Let `χ` be sum-invariant and put `Φ_χ(h) = Σ_i χ(g_i)` over a table of `h`. This is §4 of
`contracting-positive-degree-base-nontrivial-characters-proof`, for every `d` and `r`. That proof is written with values
in `Q`, but uses only additivity, so it holds verbatim over `R`. We repeat it.

- Refining row `i` into its `d` children changes the sum by `Σ_x χ(g_i|_x) − χ(g_i) = 0`.
- Two tables of `h` have a common refinement of their domain partitions. On a fixed domain partition the table is
  unique: `h(C_{α_i}) = C_{β_i}` determines `β_i`, and `G` acts faithfully on `X^ω`, so `g_i` is determined.
- Additivity: by (L2), a table of `h h'` has elements `g'_j|_z g_i`. The `g'_j|_z` over all `i` are exactly the
  elements of a refinement of the table of `h`, since the `C_{β_i}` partition `C_r`.
- `g_(α)` has the table `(α ↦ α, g)` plus identity rows. So `Φ_χ(g_(α)) = χ(g)`.

Now let `Φ in Hom(Γ, R)`.

- **(C1)** `Φ(V_{d,r}) = 0`. The Higman–Thompson group `V_{d,r} = G_{d,r}` has finite abelianization: its derived
  subgroup is simple of index at most 2 (G. Higman, *Finite presentations of infinite simple groups*, Notes on Pure
  Math. 8, ANU 1974). The same statement-level citation is used for `r = 1` in
  `rover-nekrashevych-characters-are-sum-invariant-proof`, Step 5 (a).
- **(C2) Proper cones are equivalent.** Let `C_α, C_β` be proper cones.
  - `C_r` is a union of `r` cones, and a cone is 1 cone. So each complement is a nonempty union of cones, with count
    `≡ r − 1 mod k`.
  - Splitting a cone adds `k` cones. So both complements have cone partitions with the same number of pieces.
  - Matching those by prefix replacement, together with `α w ↦ β w`, gives `σ in V_{d,r}` with
    `σ g_(α) σ^{-1} = g_(β)`.
  - So `χ_Φ(g) := Φ(g_(α))` does not depend on the proper cone `α`. It is a homomorphism, because `g ↦ g_(α)` is one.
- **(C3) Sum-invariance.** `g_(α) = s ∘ Π_{x in X} (g|_x)_(αx)`, where `s in V_{d,r}` sends `αxw ↦ α g(x) w` and is
  the identity off `C_α`. The factors have disjoint supports, and each `C_{αx}` is proper. By (C1) and (C2),
  `χ_Φ(g) = Σ_x χ_Φ(g|_x)`.
- **(C4) Reconstruction.** Refine a table of `h` once, so every `C_{α_i}` is proper. This is needed only when `r = 1`
  and the table is the single row `C_r ↦ C_r`. Then `h = σ ∘ Π_i (g_i)_(α_i)`, with `σ in V_{d,r}` the prefix
  replacement `α_i w ↦ β_i w`. So `Φ(h) = Σ_i χ_Φ(g_i) = Φ_{χ_Φ}(h)`.

So `Φ ↦ χ_Φ` and `χ ↦ Φ_χ` are inverse linear maps, by (C0) and (C4). This is item 1 of the claim.

- **(C5) Living characters.** Let `Φ != 0` and let `A` be a nonempty clopen set.
  - By (C4), `χ_Φ != 0`. Pick `g` with `χ_Φ(g) != 0`.
  - `A` contains a proper cone `C_α`: take a cone inside `A` and split it once.
  - Then `g_(α) in Γ_A`, and `Φ(g_(α)) = χ_Φ(g) != 0`.

This is the input that the "Other `r`" remark of `rover-nekrashevych-bnsr-full-via-type-one-partitions` names as missing.

## 2. Type-r blocks are copies

A nonempty clopen `A` has **type** `j mod k` if it is a disjoint union of `n ≡ j mod k` cones.

- **(T1) Well defined and invariant.**
  - Two cone partitions of `A` have a common refinement, and each split adds `k` cones. So the count is well defined
    mod `k`.
  - For `h in Γ`, refine a table of `h` until `A` is a union of domain cones. By (L1) `h` maps each of them onto a
    cone, so `h(A)` has the type of `A`.
  - `C_r` has type `r`. Say `A` has **type r** if it has type `r mod k`. Its cone count `n` then lies in `T`, so
    `n >= r_0`.
- **(T2) Merging.** A union of `j` disjoint type-`r` sets has type `j r_0 mod k`. This is `≡ r_0` iff
  `k | (j − 1) r_0` iff `k' | j − 1`, since `gcd(r_0/g_0, k') = 1`.
- **(T3) Copies.** Let `A` have type `r`. Its cone count and that of `C_r` are both `≡ r mod k`. Split cones in
  whichever has fewer until both are `M`, say `A = ⊔_{j<=M} C_{α_j}` and `C_r = ⊔_{j<=M} C_{β_j}`.
  - Put `φ(α_j w) = β_j w`, a G-local homeomorphism `A -> C_r`.
  - By (L2) and (L3), `h ↦ φ h|_A φ^{-1}` and `f ↦ (φ^{-1} f φ` extended by the identity`)` are inverse homomorphisms
    `Γ_A <-> Γ`. So `Γ_A ≅ Γ`.
- **(T4) Partition stabilizers.** Let `P = {B_1, ..., B_n}` be a clopen partition of `C_r`, with setwise stabilizer
  `Γ_P` and blockwise stabilizer `K_P`.
  - The `Γ_{B_i}` commute, because their supports are disjoint, and they meet trivially.
  - If `h in K_P`, then by (L3) each `h_i` (equal to `h` on `B_i`, identity elsewhere) is in `Γ_{B_i}`, and
    `h = h_1 ⋯ h_n`.
  - So `K_P = Γ_{B_1} × ... × Γ_{B_n}`, and `Γ_P / K_P` embeds in `Sym(n)`.
  - If every `B_i` has type `r`, then `K_P ≅ Γ^n` by (T3).
- **(T5) Transitivity.** Let `(B_1, ..., B_n)` and `(B'_1, ..., B'_n)` be ordered partitions of `C_r` into type-`r`
  sets.
  - For each `i`, the cone counts of `B_i` and `B'_i` are both `≡ r_0 mod k`. Split cones until they are equal.
  - Matching the cones of `B_i` with those of `B'_i` by prefix replacement, for all `i`, gives `σ in V_{d,r}` with
    `σ(B_i) = B'_i`.

## 3. Σ-invariants (item 2 of the claim)

Fix `m >= 1` with `Γ` of type `F_m`, and a nonzero `Φ in Hom(Γ, R)`. Put `L = m + 1` and `N = (m + 1)(k' + 1) − 1`,
so `N >= L`.

**Step 1 (the poset).**

- A **type-r partition** is a partition `P` of `C_r` into finitely many clopen blocks of type `r`. Let `b(P)` be its
  number of blocks. By (T2) applied to `C_r`, `b(P) ≡ 1 mod k'`.
- Let `𝒫` be the set of type-`r` partitions with `b(P) >= L`. Order it by `P < Q` iff `Q` strictly refines `P`.
- `Γ` acts on `𝒫` by `h·P = {h(B)}`, by (T1), and preserves `b` and the order.
- Let `Y = |𝒫|` be the order complex, and `X ⊆ Y` the full subcomplex on the vertices with `b(P) <= N`.

**Step 2 (`Y` is contractible).** `𝒫` need not be directed: see the claim's `d = 3`, `r = 2` example. We use instead a
directed union of finite subposets.

- For `ℓ >= 0`, let `R_ℓ` be the partition of `C_r` into the `n_ℓ = r d^ℓ` cones of depth `ℓ`. Let `𝒫_ℓ ⊆ 𝒫` be
  the partitions each of whose blocks is a union of cones of `R_ℓ`.
- **`𝒫_ℓ ≅ Z(n_ℓ, L)`.** Send `P in 𝒫_ℓ` to the partition of the set of cones of `R_ℓ` that it induces.
  - A block that is a union of `j` cones has type `j mod k`. So the image has all block sizes in `T`, and at least
    `L` blocks.
  - Every partition of the cones with block sizes in `T` arises.
  - The map is an order isomorphism for refinement.
  - `n_ℓ = r d^ℓ ≡ r mod k` and `n_ℓ >= r >= r_0`, so `n_ℓ in T`. This is the poset `Z(n_ℓ, L)` of
    `r-mod-k-partition-posets-truncations-highly-connected`, with that claim's `(k, r_0)` equal to ours.
- **Exhaustion.** `𝒫_ℓ ⊆ 𝒫_{ℓ+1}`, since depth-`ℓ` cones are unions of depth-`(ℓ + 1)` cones. Every clopen set is a
  union of depth-`ℓ` cones for all large `ℓ`, so every finite subset of `𝒫` lies in some `𝒫_ℓ`. Each `|𝒫_ℓ|` is a
  full subcomplex of `Y`. So `Y = ∪_ℓ |𝒫_ℓ|`, an increasing union.
- **Connectivity.** By item 4 of that claim, `|𝒫_ℓ|` is `κ(⌈n_ℓ/(L − 1)⌉)`-connected. Here `L − 1 = m >= 1`,
  `κ(s) = ⌊s/c⌋ − 3`, and `n_ℓ -> ∞`, so this connectivity tends to `∞` with `ℓ`.
- A map `S^i -> Y` has compact image. That image lies in a finite subcomplex, hence in some `|𝒫_ℓ|` that is
  `i`-connected. So the map is null-homotopic in `|𝒫_ℓ| ⊆ Y`.

All homotopy groups of `Y` vanish, and `Y` is contractible by Whitehead's theorem.

**Step 3 (`X` is `(m−1)`-connected).**

- If `Q` strictly refines `P`, then by (T2) each block of `P` is a union of `≡ 1 mod k'` blocks of `Q`, at least one
  union having more than one block. So `b(Q) − b(P)` is a positive multiple of `k'`.
- The ascending link of `P`, meaning its link in the full subcomplex on vertices with `b <= b(P)`, is the order
  complex of `{Q in 𝒫 : Q < P}`. Refinements of `P` have more blocks.
- By (T2), these `Q` are the coarsenings of `P`, other than `P`, whose blocks are unions of `≡ 1 mod k'` blocks of
  `P` and which have at least `L` blocks.
- By `one-mod-k-partition-posets-are-highly-connected` ("Use" paragraph and item 4, with its `k` equal to our
  `k' >= 1`), this is the rank selection `s(P) = min(t − 1, ⌊(n − L)/k'⌋)` of `Π^{1 mod k'}_n`, where
  `n = b(P) = t k' + 1`. It is `(s(P) − 2)`-connected.

Let `b(P) = n > N`. Then:

- `n >= (m + 1)(k' + 1) = L + (m + 1)k'`, so `⌊(n − L)/k'⌋ >= m + 1`;
- `t = (n − 1)/k' >= m + 1 + m/k' > m + 1`, so `t − 1 >= m + 1`.

Hence `s(P) >= m + 1`, and the ascending link is `(m − 1)`-connected.

- For `M >= N`, `Y_{b<=M+1}` is obtained from `Y_{b<=M}` by attaching, for each `P` with `b(P) = M + 1`, the cone
  `P * lk↑(P)` along `lk↑(P) ⊆ Y_{b<=M}`.
- Distinct such `P` have the same block count, so they are incomparable. The cones therefore meet only inside
  `Y_{b<=M}`.
- Coning off `(m−1)`-connected subcomplexes gives an `m`-connected pair.
- Every compact subset of `Y` lies in some `Y_{b<=M}`. So `(Y, X)` is `m`-connected.

Equivalently, apply (ML) of `germ-complex-and-bux-gonzalez-morse-inputs` with `h = −b`, `s` constant,
`p = −∞`, `q = −N` and `r = +∞`. Adjacent vertices have `|h(v) − h(w)| >= k' >= 1`. By Step 2,
`π_i(X) = π_i(Y) = 0` for `i <= m − 1`.

**Step 4 (cocompactness).**

- A simplex of `X` is a chain `σ = (P_0 > P_1 > ... > P_p)`, with `P_0` finest and `L <= b(P_i) <= N`. So
  `dim X <= N − L`.
- Order the blocks of `P_0`. Then `σ` is determined by the ordered partition `P_0` and a chain of partitions of the
  index set `{1, ..., b(P_0)}`. There are finitely many such chains.
- By (T5), `V_{d,r} <= Γ` is transitive on ordered type-`r` partitions with a given number of blocks. It carries the
  chain attached to an index chain to the chain attached to the same index chain.
- So `Γ` has finitely many orbits of simplices in `X`.

**Step 5 (stabilizers).**

- `Γ` preserves `b`, and the vertices of `σ` have distinct `b`. So `Stab(σ)` fixes `σ` pointwise, and
  `Stab(σ) = ∩_i Γ_{P_i}`.
- Put `n_0 = b(P_0) >= m + 1`. An element fixing every block of `P_0` fixes every union of them, so
  `K_{P_0} <= Stab(σ) <= Γ_{P_0}`.
- By (T4), `K_{P_0} = Γ_{B_1} × ... × Γ_{B_{n_0}}` with every `Γ_{B_i} ≅ Γ`, and `|Stab(σ) : K_{P_0}| <= n_0!`.
- So `K_{P_0}` and `Stab(σ)` have type `F_m`.

**Step 6 (characters on stabilizers).**

- By (C5), `Φ|_{Γ_{B_i}} != 0` for every block `B_i`. Hence `Φ|_{Stab(σ)} != 0` for every simplex.
- By `characters-living-on-m-plus-one-factors-lie-in-sigma-m`, `[Φ|_{K_{P_0}}] in Σ^m(K_{P_0})`. By (Mon), it also
  lies in `Σ^q(K_{P_0})` for every `q <= m`.
- For `dim σ < m`, put `q = m − dim σ`. By (FI) in `meinert-cocompact-action-criterion`,
  `[Φ|_{Stab(σ)}] in Σ^q(Stab(σ))`.

**Step 7 (conclusion).**

- `Γ` acts cocompactly on the `(m−1)`-connected complex `X`, by Steps 3 and 4.
- `Φ` is nonzero on every cell stabilizer.
- Cell stabilizers of dimension below `m` satisfy the Σ-hypothesis, by Steps 5 and 6.

So (MMV) gives `[Φ] in Σ^m(Γ)`. Since `Φ` was arbitrary, `Σ^m(Γ) = S(Γ)`. ∎

## Remarks

- **Why the directedness argument fails.**
  - Two type-`r` partitions `P, Q` have the common refinement `{B ∩ B'}` into clopen sets, but its blocks need not
    have type `r`.
  - Refining a block into cones changes its type to `1`, which is `≡ r` only when `r ≡ 1 mod k`.
  - For `d = 2` every type agrees, and for `r ≡ 1 mod k` cone partitions lie in `𝒫`. In both cases `𝒫` is directed,
    and Step 2 could use the original argument.
  - The claim's `d = 3`, `r = 2` example shows that no fix exists in general. The union argument of Step 2 replaces
    directedness by the high connectivity of each finite layer `𝒫_ℓ`.
- **Nonpurity is harmless.** When `1 < g_0 < k`, the layers `Z(n_ℓ, L)` are nonpure: for `k = 6` and `r_0 = 4`, a
  block of 10 cones has no refinement into type-`r` blocks. Only connectivity is needed, and Wachs's shellability for
  nonpure posets supplies it (see the poset claim).
- **Ascending links stay pure.** The coarsenings of a fixed `P` form a `1 mod k'` lattice. Only contractibility of
  `Y` needs the nonpure input.
- **No hypothesis on `G`.** As in the `r = 1` route, `G` enters only through (C0)–(C5) and the tables. Stabilizers
  are virtually `Γ^n`, so `Σ^*(V_{d,r}G)` is decided entirely by the finiteness type of `V_{d,r}G`.
