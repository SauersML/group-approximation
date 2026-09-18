---
rg: 2
id: rover-nekrashevych-bnsr-full-via-type-one-partitions
kind: route
title: Let V_d(G) act on the poset of type-one clopen partitions with between m+1 and (m+1)d-1 blocks; stabilizers are virtually powers of V_d(G) itself
target: rover-nekrashevych-bnsr-invariants-are-full
requires:
  - rover-nekrashevych-characters-are-sum-invariant
  - rover-nekrashevych-type-one-clopen-stabilizers-are-copies
  - one-mod-k-partition-posets-are-highly-connected
  - meinert-cocompact-action-criterion
  - characters-living-on-m-plus-one-factors-lie-in-sigma-m
  - germ-complex-and-bux-gonzalez-morse-inputs
---

Notation as in `rover-nekrashevych-type-one-clopen-stabilizers-are-copies` (cited as **Copies**, items 1–6): `d >= 2`,
`k = d − 1`, `G <= Aut(T_d)` self-similar, `Γ = V_d(G)`, `C = X^N`.

**Item 1** of the target is item 2 of `rover-nekrashevych-characters-are-sum-invariant`, word for word:

- `Φ -> (g -> Φ(g_(u)))` is a linear isomorphism onto `{χ : ψχ = χ}`;
- `ψχ = χ` is the stated identity `χ(g) = Σ_x χ(g|_x)`.

**Item 2.** Fix `m >= 1` with `Γ` of type `F_m` and a nonzero `Φ in Hom(Γ,R)`. We show `[Φ] in Σ^m(Γ)`. Put
`L = m + 1` and `N = (m + 1)d − 1`, so `N >= L`.

**Step 1 (the poset).**

- A *type-1 partition* is a partition `P` of `C` into finitely many clopen blocks, each of type 1. Let `b(P)` be its
  number of blocks. The cone counts add up to `≡ 1`, so `b(P) ≡ 1 mod k`.
- Let `𝒫` be the set of type-1 partitions with `b(P) >= L`, ordered by `P < Q` iff `Q` strictly refines `P`.
- `Γ` acts on `𝒫` by `h·P = {h(B)}`, by Copies 1, and preserves `b` and the order.
- Let `Y = |𝒫|` be the order complex, and `X ⊆ Y` the full subcomplex on the vertices with `b(P) <= N`.

**Step 2 (`Y` is contractible).**

- `𝒫` is directed. Given `P, Q`, the nonempty sets `B ∩ B'` (`B in P`, `B' in Q`) form a clopen partition. Cutting each
  into cones gives `R`, with at least `max(b(P), b(Q)) >= L` blocks, each a cone and hence type 1. So `R in 𝒫` and `R`
  refines `P` and `Q`.
- A finite subcomplex `K ⊆ Y` has finitely many vertices, all refined by one `R in 𝒫`. Every simplex of `K` together
  with `R` is a chain, so `K` lies in the closed star of `R`, which is a cone.
- So every map `S^i -> Y` is null-homotopic, and `Y` is contractible by Whitehead's theorem.

**Step 3 (`X` is `(m−1)`-connected).** Put `h(P) = −b(P)` on vertices, extended affinely on simplices, and take `s`
constant.

- Comparable vertices have different numbers of blocks, and these differ by a multiple of `k`, so `|h(v) − h(w)| >= 1`
  on edges. So `(h, s)` is a Morse function in the sense of (ML) in `germ-complex-and-bux-gonzalez-morse-inputs`.
- Sublevel sets are taken to be full subcomplexes on vertices, as there.
- The ascending link of `P` is spanned by the adjacent vertices with larger `h`: the `Q in 𝒫` with `Q < P`. That is,
  the coarsenings of `P` into at least `L` blocks that are type-1 partitions, other than `P`.
- A union of `j` type-1 blocks has type `j mod k`. So these are the coarsenings whose blocks are unions of `≡ 1 mod k`
  blocks of `P`.
- By `one-mod-k-partition-posets-are-highly-connected`, "Use" paragraph and item 4, this is the rank selection
  `s(P) = min(t − 1, ⌊(n − L)/k⌋)` of `Π^{1 mod k}_n`, where `n = b(P) = tk + 1`. It is `(s(P) − 2)`-connected.

Let `b(P) = n > N`. Then:

- `n >= (m+1)(k+1) = L + (m+1)k`, so `⌊(n − L)/k⌋ >= m + 1`;
- `t = (n − 1)/k >= m + 1 + m/k > m + 1`, so `t − 1 >= m + 1`.

Hence `s(P) >= m + 1`, and every ascending link of a vertex with `h < −N` is `(m−1)`-connected.

(ML), with `p = −∞`, `q = −N`, `r = +∞`, says the pair `(Y, X)` is `m`-connected. `Y` is contractible by Step 2, so
`π_i(X) = π_i(Y) = 0` for `i <= m − 1`.

*Direct check, independent of (ML).* `Y_{b<=M+1}` is obtained from `Y_{b<=M}` as follows. For each `P` with
`b(P) = M + 1`, attach the cone `P * lk↓(P)` along `lk↓(P) ⊆ Y_{b<=M}`. Distinct such `P` are incomparable, so the
cones meet only inside `Y_{b<=M}`. Coning off `(m−1)`-connected subcomplexes gives an `m`-connected pair. Every compact
subset of `Y` lies in some `Y_{b<=M}`.

**Step 4 (cocompactness).**

- A simplex of `X` is a chain `σ = (P_0 > P_1 > ... > P_p)`, with `P_0` finest and `L <= b(P_i) <= N`. So
  `dim X <= N − L`.
- Order the blocks of `P_0`. Then `σ` is determined by the ordered partition `P_0` and a chain of partitions of the
  index set `{1, ..., b(P_0)}`. There are finitely many such chains.
- By Copies 5, `V_d` is transitive on ordered type-1 partitions with a given number of blocks.
- So `Γ` has finitely many orbits of simplices in `X`.

**Step 5 (stabilizers).**

- `Γ` preserves `b`, and the vertices of `σ` have distinct `b`. So `Stab(σ)` fixes `σ` pointwise and equals
  `∩_i Γ_{P_i}`.
- Put `n_0 = b(P_0) >= L = m + 1`. An element fixing every block of `P_0` fixes every union of them, so
  `K_{P_0} <= Stab(σ) <= Γ_{P_0}`.
- By Copies 4, `K_{P_0} = Γ_{B_1} × ... × Γ_{B_{n_0}}` with every `Γ_{B_i} ≅ Γ`, and `|Stab(σ) : K_{P_0}| <= n_0!`.
- `Γ` has type `F_m`. So `K_{P_0}` has type `F_m`, being a finite product of `F_m` groups, and so does its finite-index
  overgroup `Stab(σ)`.

**Step 6 (characters on stabilizers).**

- By Copies 6, `Φ|_{Γ_{B_i}} != 0` for every block. Hence `Φ|_{Stab(σ)} != 0` for every simplex.
- `Φ|_{K_{P_0}} = (Φ|_{Γ_{B_1}}, ..., Φ|_{Γ_{B_{n_0}}})` is a character of a product of `n_0 >= m + 1` groups of type
  `F_m`, nonzero on every factor.
- By `characters-living-on-m-plus-one-factors-lie-in-sigma-m`, `[Φ|_{K_{P_0}}] in Σ^m(K_{P_0})`. By (Mon), it also lies
  in `Σ^q(K_{P_0})` for every `q <= m`.
- Let `dim σ < m` and `q = m − dim σ`. `Stab(σ)` has type `F_q` and `K_{P_0}` has finite index. By (FI) in
  `meinert-cocompact-action-criterion`, `[Φ|_{Stab(σ)}] in Σ^q(Stab(σ))`.

**Step 7 (conclusion).** `Γ` acts cocompactly on the `(m−1)`-connected complex `X` (Steps 3–4).

- `Φ` is nonzero on every cell stabilizer.
- For `dim σ < m`, `Stab(σ)` has type `F_{m − dim σ}` and `[Φ|_{Stab(σ)}] in Σ^{m − dim σ}(Stab(σ))` (Steps 5–6).

(MMV) in `meinert-cocompact-action-criterion` gives `[Φ] in Σ^m(Γ)`. `Φ` was arbitrary, so `Σ^m(Γ) = S(Γ)`. ∎

## Remarks

- **No hypothesis on `G`.** The proof never uses finiteness properties of `G`, contraction, bounded activity or even
  finite generation of `G`. It needs only that `Γ` itself has type `F_m`, which item 2 assumes.
  - Stabilizers are virtually `Γ^n`, not `G^n`, so the Basilica obstruction noted in the target does not arise.
  - This also covers `rover-nekrashevych-higher-sigma-invariants-are-full`, the case where `G` has type `F_m`. That
    claim keeps its own routes.
- **Why the bottom truncation.** Partitions with fewer than `m + 1` blocks are excluded so that every stabilizer is a
  product of at least `m + 1` living factors. Without it, a vertex such as a two-block partition has stabilizer
  virtually `Γ × Γ`. The claim would then need `Σ^m(Γ × Γ)`, which Meinert's inequality reduces to `Σ^{m−1}(Γ) = S`.
  That gives an alternative proof by induction on `m`, using the full proper part (item 3 of the poset claim) in place
  of rank selection.
- **Not circular.** The copies of `Γ` in the stabilizers make this complex useless for proving finiteness properties
  of `Γ` (compare `thompson-v-coset-stabilizers-contain-copies-of-v`). The Σ-criterion, however, takes the finiteness
  of `Γ` as input.
- **Other `r`.** For `V_{d,r}(G)` the same argument runs on partitions into blocks of type `r`: coarsenings are
  `1 mod k/gcd(r,k)` partitions, and stabilizers are virtually `V_{d,r}(G)^n`. The missing input is the analogue of
  Copies 6, the character description of `V_{d,r}(G)`. It is not claimed here.

## Attempts

- 2026-09-18 (w6-101): the "Other `r`" remark needs one more change besides the character input.
  - Step 2's directedness fails when `gcd(r, d−1) > 1`. For `d = 3` and `r = 2`, `{C_0 ∪ C_{10}, C_{11} ∪ C_{12}}`
    and `{C_0 ∪ C_{11}, C_{10} ∪ C_{12}}` meet in single cones, which have odd type, so they have no common type-2
    refinement.
  - Both gaps are closed in `rover-nekrashevych-vdr-sigma-full-via-type-r-partitions`:
    - the characters of `V_{d,r}G`, with living on clopen sets;
    - contractibility, as a directed union of truncated `r mod k` partition posets
      (`r-mod-k-partition-posets-truncations-highly-connected`).
