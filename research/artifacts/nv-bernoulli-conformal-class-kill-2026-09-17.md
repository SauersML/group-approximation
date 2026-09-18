# Bernoulli conformal pinning: spatial realizations of 2-graph groupoids in `G_2^n`

Lane `swarm-0917-w5-nv-rel-t`, 2026-09-17. This continues the route of
`some-brin-thompson-group-has-an-infinite-kazhdan-subgroup` through
`[[Λ_T]] ↪ mV` (artifact `nv-brick-codings-of-two-graphs-2026-09-17.md`). That artifact
killed edge-wise brick codings using Lebesgue measure and the Kraft equality, for `q` not
a power of 2 (and by SAT for five `PG(2,2)` presentations). It left open (1) block
recodings, (2) groupoid-level spatial embeddings, (4) `q = 2^r`.

The new input is to use the whole **Bernoulli family** `μ_p`, `p ∈ (0,1)^n`, instead of
one measure. Each `μ_p` pulls back to a quasi-invariant measure on the path space, and
Perron–Frobenius pins its Radon–Nikodym class whenever that class lies in the degree
plane. A class independent of `p` forces every letter-count cocycle to be a coboundary,
and a bounded-offset argument then bounds orbits. No Kraft equality, no integrality, no
SAT, and no hypothesis on `q`.

## 0. Conventions

**Cuntz product groupoid.** `C = {0,1}^N`. `G_2^n` is the set of triples `(x, k, y)` with
`x, y ∈ C^n`, `k ∈ Z^n`, such that for each coordinate `i` there are words `u_i, v_i` and a
tail `w_i` with `x_i = u_i w_i`, `y_i = v_i w_i`, `|u_i| - |v_i| = k_i`. Range `x`, source
`y`. Its topology has basis the sets `[u, v] = {(u w, |u| - |v|, v w)}` (word tuples
`u, v`), so it is ample and each `[u,v]` is a compact open bisection acting by the
canonical prefix replacement `v w ↦ u w`.

**Letter-count cocycles.** For `g = (u w, k, v w)` put
`N^ε_i(g) = #_ε(u_i) - #_ε(v_i)` for `ε ∈ {0,1}`. This does not depend on the choice of
`(u_i, v_i, w_i)`: two choices with the same `k_i` differ by moving a common word from the
tail to both prefixes. So `N^ε_i` is a continuous `Z`-valued cocycle (locally constant on
each `[u,v]`), and `c_i := N^0_i + N^1_i = k_i` is the offset cocycle.

**Bernoulli measures.** For `p ∈ (0,1)^n` let `μ_p = ⊗_i β_{p_i}^{⊗N}` with
`β_t(1) = t`. For a word tuple `u`, `μ_p([u]) = w_p(u) := ∏_i p_i^{#_1(u_i)} (1-p_i)^{#_0(u_i)}`.
For the bisection `[u,v]` and Borel `A ⊆ [v]`,
`μ_p(α(A)) = ∫_A exp D_p(g_y) dμ_p(y)`, where `α(v w) = u w`, `g_y` is the element of
`[u,v]` with source `y`, and

    D_p(g) = Σ_i ( N^1_i(g) log p_i + N^0_i(g) log(1 - p_i) ).

(Indeed `μ_p([u z]) = w_p(u) μ'(z) = (w_p(u)/w_p(v)) μ_p([v z])` for tail words `z`.)
`D_p` is a continuous real cocycle.

**2-graph groupoid.** `Λ` is a finite 2-graph with vertex set `Λ^0`, no sources (every
vertex is the range of edges of both colours). `Λ^∞` is its infinite path space,
`Z(λ) ⊆ Λ^∞` the cylinders, `σ^m` the shifts, and
`G_Λ = {(x, m - n, y) : σ^m x = σ^n y}` the Kumjian–Pask path groupoid, with basic compact
open bisections `Z(λ, μ) = {(λz, d(λ) - d(μ), μz)}`. The colour matrices are
`M_j(w, v) = #{edges e of colour j : r(e) = w, s(e) = v}`. The degree cocycles are
`d_j(x, k, y) = k_j`. `H^1(G; R)` means continuous real cocycles modulo `h∘r - h∘s` with `h`
continuous on the unit space. Only the definitions of `Λ^∞`, `Z(λ,μ)`, unique
factorization and the fact that the cylinders of a fixed degree `(j,0)` partition `Λ^∞`
are used; these are part of the definition of a 2-graph and its path space.

**Spatial realization.** A spatial realization of `G_Λ` in `G_2^n` is a continuous
groupoid homomorphism `ι : G_Λ -> G_2^n` whose restriction `h = ι|_{Λ^∞}` is a
homeomorphism onto a compact **open** set `U ⊆ C^n`. No injectivity off the unit space
and no openness of `ι` is required.

## 1. Pulled-back Bernoulli measures

**Lemma 1.1.** Let `ι` be a spatial realization with `h = ι|_{Λ^∞}` and `ν_p(A) := μ_p(h(A))`.
Then `ν_p` is a finite Borel measure with `ν_p(Z(v)) > 0` for every vertex `v`, and for every
path `λ` and Borel `A ⊆ Z(s(λ))`,

    ν_p(λA) = ∫_A exp( D_p(ι(λy, d(λ), y)) ) dν_p(y).

*Proof.* `h(Z(v))` is a nonempty open subset of `C^n`, so it has positive `μ_p`-measure.
`T = ι(Z(λ, s(λ)))` is compact, as a continuous image of a compact set. On `T` the maps
`s` and `r` are injective, because `s∘ι = h∘s` and `r∘ι = h∘r` with `h` injective. So `T`
is a bisection with partial map `α_T(h(y)) = h(λy)`. Cover `T` by finitely many basic
bisections `[u_1,v_1], …, [u_r,v_r]`. On the relatively open set `T ∩ [u_j, v_j]` the
partial map of `T` equals the canonical map of `[u_j, v_j]`, so Section 0 gives the density
`exp D_p(ι(·))` piece by piece. Hence
`ν_p(λA) = μ_p(α_T(h(A))) = ∫_A exp D_p(ι(λy,d(λ),y)) dν_p(y)`. ∎

**Lemma 1.2 (Perron pinning).** Let `ν` be a finite Borel measure on `Λ^∞` with
`ν(Z(v)) > 0` for all `v`, and `c` a continuous real cocycle on `G_Λ` with
`ν(λA) = ∫_A e^{c(λy, d(λ), y)} dν(y)` for all `λ` and `A ⊆ Z(s(λ))`. If
`c = a d_1 + b d_2 + H∘r - H∘s` with `H` continuous, then `e^{-a} = ρ(M_1)` and
`e^{-b} = ρ(M_2)`.

*Proof.* Put `ν' = e^{-H} ν`. Since `H` is bounded, `ν'` is finite and `ν'(Z(v)) > 0`.
For `A ⊆ Z(s(λ))`,
`ν'(λA) = ∫_A e^{-H(λy)} e^{a d_1(λ) + b d_2(λ) + H(λy) - H(y)} dν(y) = e^{a d_1(λ) + b d_2(λ)} ν'(A)`.
Take `j ≥ 1` and the paths `λ` of degree `(j,0)`. Their cylinders partition `Λ^∞`, so

    ν'(Λ^∞) = Σ_{d(λ) = (j,0)} ν'(Z(λ)) = e^{aj} Σ_{w, v} M_1^j(w, v) ν'(Z(v)).

Let `m_+` and `m_-` be the max and min over `v` of `ν'(Z(v))`, both in `(0, ∞)`, and let
`‖M‖_Σ` be the sum of the entries. Then
`m_- e^{aj} ‖M_1^j‖_Σ ≤ ν'(Λ^∞) ≤ m_+ e^{aj} ‖M_1^j‖_Σ`. Taking `j`-th roots and using
Gelfand's formula (`‖·‖_Σ` is a norm on matrices) gives `e^{a} ρ(M_1) = 1`. Colour 2 is the
same. ∎

**Lemma 1.3 (the degree plane is a plane).** If `s d_1 + t d_2 = H∘r - H∘s` with `H`
continuous, then `s = t = 0`.

*Proof.* For `y ∈ Λ^∞` and `j ≥ 1` put `y' = σ^{(j,0)} y`. Then `(y, (j,0), y') ∈ G_Λ` gives
`sj = H(y) - H(y')`, which is bounded in `j`. So `s = 0`, and likewise `t = 0`. ∎

## 2. Bounded offsets bound the fibres

**Lemma 2.1.** Let `𝒢 ⊆ G_2^n` be a subgroupoid with unit space `U`. Suppose every element
of `𝒢` is a finite product of elements of `B ∪ B^{-1}`, where `B` is a finite family of
compact bisections of `G_2^n` contained in `𝒢`. Suppose also that for each `i` there is a
bounded function `F_i : U -> R`, not necessarily continuous, with
`c_i(g) = F_i(r(g)) - F_i(s(g))` on `𝒢`. Then there is `N` with
`#{g ∈ 𝒢 : s(g) = x} ≤ N` for every `x ∈ U`.

*Proof.*
1. *Integer transfer.* `c_i` is integer-valued, so `F_i(r g) - F_i(s g) ∈ Z`. Hence the
   fractional part of `F_i` is constant along `𝒢`-orbits, and `⌊F_i⌋` satisfies the same
   identity. Replace `F_i` by `⌊F_i⌋`. Now `F_i` is integer-valued with `|F_i| ≤ M`.
2. *Depth bound.* Each bisection in `B ∪ B^{-1}` is compact, so it is covered by finitely
   many basic `[u,v]`. So there is `D` such that every `b ∈ B ∪ B^{-1}` is represented as
   `(u w, |u| - |v|, v w)` with `|u_i|, |v_i| ≤ D`.
3. *Canonical bricks.* Put `L = D + M`. For `x ∈ U` let `P(x)_i = x_i|_{L + F_i(x)}`, a word
   of length between `D` and `D + 2M`.
   **Claim:** every `g ∈ 𝒢` with source `x` has the form `g = (P(rg) w, c(g), P(x) w)`.
   The proof is by induction on the word length of `g`; for a unit it is trivial.
   - Let `g = b g'` with `b ∈ B ∪ B^{-1}`, `z = r(g') = s(b)`, and `g' = (P(z) w, ·, P(x) w)`.
     Represent `b` by `(u, v)` with `|u_i|, |v_i| ≤ D`.
   - Both `v_i` and `P(z)_i` are prefixes of `z_i`, and `|P(z)_i| = L + F_i(z) ≥ D ≥ |v_i|`.
     So `P(z)_i = v_i t_i`, and since `z = P(z) w`, `b = (u t w, ·, v t w)`. Then
     `g = (u t w, c(g), P(x) w)`.
   - The prefix `u_i t_i` of `r(g)_i` has length
     `|u_i| - |v_i| + L + F_i(z) = c_i(b) + L + F_i(z) = L + F_i(r g)`. So `u t = P(r g)`.
4. *Count.* By the claim, `g` with `s(g) = x` is determined by `x` and the tuple of words
   `P(r g)`, each of length at most `D + 2M`. So `N = ∏_i 2^{D + 2M + 1}` works. ∎

## 3. The theorem

**Theorem 3.1.** Let `Λ` be a finite 2-graph without sources with `ρ(M_1) > 1`, and let
`ι : G_Λ -> G_2^n` be a spatial realization. Then the letter-count classes
`κ^ε_i := [N^ε_i ∘ ι] ∈ H^1(G_Λ; R)` (`1 ≤ i ≤ n`, `ε ∈ {0,1}`) are **not all** contained in
the degree plane `R[d_1] + R[d_2]`.

*Proof.* Suppose every `κ^ε_i = α^ε_i [d_1] + β^ε_i [d_2]`. By Lemma 1.3 these coefficients
are unique.

1. *Every Bernoulli class is in the plane.* `D_p ∘ ι = Σ_i N^1_i∘ι log p_i + N^0_i∘ι log(1-p_i)`,
   so `D_p∘ι = a(p) d_1 + b(p) d_2 + H_p∘r - H_p∘s` with
   `a(p) = Σ_i α^1_i log p_i + α^0_i log(1 - p_i)` (and `b(p)` likewise with `β`) and `H_p`
   continuous.
2. *Perron pins it.* By Lemma 1.1, `ν_p` and `c = D_p∘ι` satisfy the hypotheses of Lemma 1.2.
   So `a(p) = -log ρ(M_1)` and `b(p) = -log ρ(M_2)` for every `p ∈ (0,1)^n`.
3. *All letter classes vanish.* Differentiating `a(p)` in `p_i` gives
   `α^1_i / p_i - α^0_i / (1 - p_i) = 0` for all `p_i ∈ (0,1)`, so `α^1_i = α^0_i = 0`.
   Likewise every `β^ε_i = 0`. So every `κ^ε_i = 0`, and each offset cocycle
   `c_i∘ι = (N^0_i + N^1_i)∘ι` equals `H_i∘r - H_i∘s` with `H_i` continuous, hence bounded, on
   the compact space `Λ^∞`.
4. *Bounded fibres.* `𝒢 = ι(G_Λ)` is a subgroupoid with unit space `U`: if `ι(g), ι(g')` are
   composable then `h(s g) = h(r g')`, so `g, g'` are composable. Let
   `B = {ι(Z(e, s(e))) : e an edge}`, a finite family of compact bisections (Lemma 1.1).
   Every element `(λz, d(λ) - d(μ), μz)` of `G_Λ` equals
   `(λz, d(λ), z)(μz, d(μ), z)^{-1}`, and `(λz, d(λ), z)` is a product of edge elements by
   factorization of `λ` into edges. So `B` generates `𝒢` as in Lemma 2.1, with
   `F_i = H_i∘h^{-1}` bounded. Lemma 2.1 gives `N` bounding every source fibre of `𝒢`.
5. *Contradiction.* For `y ∈ Λ^∞` and `j ≥ 1`, the elements `ι(λy, (j,0), y)` with
   `d(λ) = (j,0)` and `s(λ) = r(y)` have source `h(y)` and pairwise distinct ranges `h(λy)`.
   So every column sum of `M_1^j` is at most `N` (every vertex is `r(y)` for some `y`, as
   there are no sources). Then `‖M_1^j‖_Σ ≤ N |Λ^0|` for all `j`, so `ρ(M_1) ≤ 1`, a
   contradiction. ∎

**Corollary 3.2 (cocycle rigidity kills every spatial realization).** Let `Λ` be as in 3.1,
and suppose every locally constant real cocycle on `G_Λ` is cohomologous (with a continuous
transfer function) to some `a d_1 + b d_2`. Then `G_Λ` has no spatial realization in any
`G_2^n`.

*Proof.* `N^ε_i` is locally constant and `ι` is continuous, so `N^ε_i∘ι` is a locally
constant cocycle. By hypothesis, every `κ^ε_i` lies in the degree plane, which contradicts
Theorem 3.1. ∎

Only locally constant cocycles are needed. Continuous real cocycles in general form a much
larger space (for the full shift, Hölder versus continuous), and nothing about them is
claimed.

**Corollary 3.3 (brick codings die at square-complex rigidity, for every `q`).** Let `Λ` be
a finite 2-graph without sources with `ρ(M_1) > 1` and `dim_R H^1(K(Λ); R) = 2`, where
`K(Λ)` is the square complex (vertices, edges of both colours, one 2-cell per square). Then
`Λ` has no brick coding (B1)–(B3) in any dimension `m`.

*Proof.* Suppose `φ` is a brick coding. By `brick-coded-two-graph-full-groups-embed-in-brin-thompson`
(Theorem A of `nv-brick-codings-of-two-graphs-2026-09-17.md`) there is a homeomorphism
`h : Λ^∞ -> ⊔_a C^m` with `h(λz) = φ(λ) h(z)`, where `φ` is extended multiplicatively to
paths. Choose word tuples `π_a` (`a ∈ Λ^0`) whose bricks partition `C^m` and put
`χ(a, w) = π_a w`. Define

    ι(λz, d(λ) - d(μ), μz) = ( π_{r(λ)} φ(λ) h(z),  k,  π_{r(μ)} φ(μ) h(z) ),
    k_i = |π_{r(λ),i} φ_i(λ)| - |π_{r(μ),i} φ_i(μ)|.

- Replacing `(λ, μ, z)` by `(λν, μν, z')` with `z = νz'` gives the same triple, because
  `φ(λν) h(z') = φ(λ) h(νz')`. Representations of an element of `G_Λ` differ exactly by
  such common extensions (unique factorization).
- So `ι` is a well-defined continuous homomorphism, locally constant in the words. On units
  it is `χ∘h`, a homeomorphism onto `C^m`. So `ι` is a spatial realization.
- Let `n^ε_i(λ) = #_ε(φ_i(λ))`. By (B2) it is additive on paths, and on edges it is a
  1-cocycle of `K(Λ)`. By `dim H^1(K(Λ)) = 2` and Lemma 1.3's cycle argument on `K(Λ)`, it
  equals `α d_1 + β d_2 + δg` for a vertex function `g`. Telescoping along paths gives
  `n^ε_i(λ) = α d_1(λ) + β d_2(λ) ± (g(r λ) - g(s λ))`.
- Hence on `Z(λ, μ)`, `N^ε_i∘ι = α d_1 + β d_2 + H∘r - H∘s` with
  `H(x) = ±g(r(x)) + #_ε(π_{r(x),i})`, which is continuous. So every `κ^ε_i` is in the degree
  plane, contradicting Theorem 3.1. ∎

(The sign `±` is fixed by the orientation convention for `δ` and plays no role.)

**Corollary 3.4 (block recodings).** Let `Λ^{[k]}` be the higher-block 2-graph whose
vertices are the rectangles of degree `(k,k)` of `Λ`, colour-`j` edges the rectangles of
degree `(k,k) + e_j`, and squares the rectangles of degree `(k+1,k+1)`. It has no sources, since every rectangle extends. Its colour-1 paths
of length `j` are the rectangles of degree `(j+k, k)`. Each colour-1 path of `Λ` of degree
`(j+k, 0)` extends to at least one such rectangle, and distinct paths give distinct
rectangles. So `‖(M_1^{[k]})^j‖_Σ ≥ ‖M_1^{j+k}‖_Σ` and `ρ(M_1^{[k]}) ≥ ρ(M_1) > 1`.
Hence if `dim H^1(K(Λ^{[k]}); R) = 2`, then `Λ^{[k]}` has no brick coding in any
dimension.

## 4. Computation: `H^1` of the block square complexes

Scripts: `experiments/nv-conformal-rigidity-2026-09-17/block_h1.py` and `run_block_h1.py`.
They reuse `rs2graph.py`, `tp.py` and `rank_mod_p` from
`experiments/nv-brick-coding-2026-09-17/`.

**Complex.** For level `k`, `K_k := K(Λ^{[k]})` has cochains
`C^0 = R^{(k,k)-blocks} -> C^1 = R^{(k+1,k)-blocks} ⊕ R^{(k,k+1)-blocks} -> C^2 = R^{(k+1,k+1)-blocks}`,
with `δ_0 h = (h∘σ_1 - h, h∘σ_2 - h)` and
`δ_1 φ(B) = φ_1(B|_{(k+1,k)}) + φ_2(σ_1 B|_{(k,k+1)}) - φ_2(B|_{(k,k+1)}) - φ_1(σ_2 B|_{(k+1,k)})`.
Level 0 is the square complex of `certificate.py`. A locally constant cocycle on `G_Λ` is a
pair `(φ_1, φ_2)` of locally constant functions with the square identity. So the group of
locally constant cocycles modulo locally constant coboundaries is `colim_k H^1(K_k)`. This
description is used only as evidence and is not part of any established node. The colimit is taken along the pullbacks, and a class at
level `k` may still die at a higher level.

**Bounds.**
- *Upper bound:* `dim H^1(K_k) ≤ dim C^1 - rank_{GF(p)} δ_1 - (dim C^0 - #components)`, with
  `p = 1000003`, since `rank_GF(p) ≤ rank_Q`. `h1_fast` gauge-fixes a spanning tree, applies
  exact 1- and 2-term substitutions, and eliminates the rest over `GF(p)`. It is
  cross-checked against the plain elimination `h1_level` (logs mark "cross-checked").
- *Lower bound 2:* a coboundary sums to 0 around a closed colour-1 path, while `d_1` does
  not; the same holds for colour 2.

**Results** (`block_h1_pg22_k1.log`, `product_control.log`):

| 2-graph | k | V | E | F | dim H^1(K_k) |
|---|---|---|---|---|---|
| RS `PG(2,2)` T0–T4 | 0 | 42 | 336 | 672 | 2 |
| RS `PG(2,2)` T0–T4 | 1 | 672 | 5376 | 10752 | 2 |
| product of two full 4-shifts | 0 | 16 | 128 | 256 | 26 |
| product of two full 4-shifts | 1 | 256 | 2048 | 4096 | 98 |
| product of two full 4-shifts | 2 | 4096 | 32768 | 65536 | 386 |

The control follows `2 + 24·4^k`: for a product the letter classes of each factor survive,
because `H^1(G_4)` has infinite rank (Livšic). The Ã₂ examples stay at 2.

**Consequence (certificate).** By Corollary 3.4, the level-1 block recodings `Λ_T^{[1]}` of
the five `PG(2,2)` presentations T0–T4 admit no brick coding in any dimension. By
Corollary 3.3 at level 0, `Λ_T` itself admits none, which re-proves
`cmsz-pg22-rs-two-graphs-admit-no-brick-coding` without SAT. It also re-proves
`cmsz-pg23-rs-two-graphs-admit-no-brick-coding` from its `dim H^1 = 2` certificate,
without the Kraft equality.

## 5. What is killed, what survives, and the one prerequisite left

**Killed class.** Every realization of (P3) `[[Λ_T]] ↪ mV` that comes from a spatial
realization of the groupoid `G_{Λ_T}` in `G_2^n`, *provided* `Λ_T` is cocycle-rigid.
- *Invariant:* the Bernoulli conformal classes `p ↦ [D_p∘ι] ∈ H^1(G_Λ; R)`, pinned by the
  Perron eigenvalues.
- *Where every member dies:* Step 3 of Theorem 3.1. A `p`-independent class forces every
  letter class to vanish, and Lemma 2.1 then bounds the orbits of a groupoid whose orbits
  grow like `ρ(M_1)^j`.
- *Unconditionally killed now:* brick codings of `Λ_T` whenever `dim H^1(K(Λ_T)) = 2`
  (every `q`, including `q = 2^r`), and brick codings of `Λ_T^{[k]}` whenever
  `dim H^1(K(Λ_T^{[k]})) = 2`, verified for T0–T4 at `k ≤ 1`.

**The prerequisite (OPEN).** `robertson-steger-two-graph-groupoids-are-cocycle-rigid`:
every locally constant real cocycle on `G_{Λ_T}` is cohomologous to `a d_1 + b d_2`.
Equivalently, the direct limit of `H^1(K_k)` from Section 4 is 2-dimensional, if the
colimit description is accepted; that description is standard but not written out here. By
Corollary 3.2 this single statement kills survivors (1) block recodings, (2) groupoid-level
spatial embeddings and (4) `q = 2^r` of the earlier artifact at once, for every `q`.
- *Evidence:* the table in Section 4.
- *Why it may fail:* the colimit can create classes at high `k` that are invisible at
  every finite level only if `H^1(K_k)` grows, and it did not for `k ≤ 1`. Heuristically,
  Katok–Spatzier rigidity for higher-rank abelian actions uses the commutation of the two
  expanding directions, which holds in Ã₂ and fails for products of trees, where the
  control grows.
- *No import found:* no cocycle-rigidity theorem for `k`-graph groupoids of Ã₂ type was
  located. For Bruhat–Tits cases, Shapiro's lemma gives
  `H^1(Γ, C^∞(G/B)) ≅ H^1_sm(B, C^∞(Γ\G))`, and the unipotent part is a `lim^1` term that
  still needs an argument. This was not completed.

**Survivors.** (3) non-spatial abstract embeddings `[[Λ_T]] ↪ mV` or `Γ_T ↪ mV` that do
not come from a groupoid map; (5) Kazhdan groups not of Ã₂ type; and, until the rigidity
claim is proved, spatial realizations of `G_{Λ_T}` not coming from a finite-level brick
coding.

## 6. Remark: the subgroup version

The same two ingredients give a criterion inside `nV`. Let `K ≤ nV` be finitely generated
and let `[D_p|_K] ∈ H^1(K ⋉ C^n; R)` (continuous cocycles on the transformation groupoid
modulo continuous coboundaries). Then `K` is finite iff `p ↦ [D_p|_K]` is constant.
- *If finite:* averaging gives transfer functions.
- *If constant:* Step 3 above gives `c_i|_K = H_i∘r - H_i∘s` with `H_i` bounded, and the
  brick argument of Lemma 2.1 (generators of bounded depth) lets `K` act faithfully on a
  finite set of bricks.

This is a reformulation of Step 6 of
`research/artifacts/fg-subgroups-of-nv-finite-iff-germ-finite-proof-2026-09-17.md`
(bounded transfer of the offset cocycle), not a new node. It says an infinite Kazhdan
subgroup of `nV` must carry uncountably many pairwise non-cohomologous Bernoulli
Radon–Nikodym classes. Theorem 3.1 is the groupoid-level analogue that sees the
Perron constraint.
