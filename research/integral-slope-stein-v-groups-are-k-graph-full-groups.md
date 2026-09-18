---
rg: 2
id: integral-slope-stein-v-groups-are-k-graph-full-groups
kind: claim
title: For multiplicatively independent integers n_1..n_k >= 2, Stein's group V(Z[1/n_1...n_k], <n_1..n_k>) is the topological full group of an explicit one-vertex k-graph, hence of type F_infinity with a finite-index simple derived subgroup, and it acts with type (A) on its breakpoints; V_{2,3} is itself simple
requires:
  - stein-v-groups-act-with-type-a-on-breakpoints
  - ct-p-z-is-a-one-vertex-k-graph-full-group
distinct_from:
  stein-groups-t23-and-v23-are-finitely-presented: that is the OPEN node asking for finite presentation of T_{2,3} and V_{2,3}, stuck on an unread identification of Cantor-algebra models with the piecewise-linear groups; this proves the V half for all integral slope sets directly in the piecewise-linear model, through Li's k-graph finiteness theorem, and leaves T_{2,3} open.
  ct-p-z-is-a-one-vertex-k-graph-full-group: that identifies Kohl's CT_P(Z) with the full group of a one-vertex k-graph (least significant digit first); the k-graph here has the same edge counts and the opposite composition (most significant digit first), so the two groups share all homology, and whether they are isomorphic is left open.
  pisot-stein-groups-are-contracting-rsgs: that treats one algebraic slope through a contracting coding; several independent slopes are never contracting in an affine coding (pisot-number-slope-stein-groups-are-contracting-rsgs, item 5), and here the commuting integral subdivisions supply a Garside structure instead.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed). Matui, arXiv:2412.05492, l. 851–856
(read at source), attributes `F_∞` of these groups and their abelianizations to Stein, Trans. AMS 332
(1992), which was not read. The proof below does not use Stein's paper. Its inputs were read at source
for `ct-p-z-is-a-one-vertex-k-graph-full-group`:
- Li, arXiv:2110.04505v2, Cor. `intro:deg` and Cor. `cor:OneVertex` (l. 2172);
- Farsi–Kumjian–Pask–Sims, arXiv:1808.07807, Thm. `thm:H computation` (l. 2252);
- Li, arXiv:2209.08087, Cor. `cor:AHConj` (l. 3155);
- Matui, arXiv:1210.5800, Thm. `simple2`;
- Tanner, arXiv:2312.07375: Thm. `fg v type` (finite generation) and the normal form of pieces.
The identification `I_l ⋉ ∂Ω = G_Λ` for a finite one-vertex k-graph is standard and was not re-read,
exactly as in `ct-p-z-is-a-one-vertex-k-graph-full-group`.

## Statement

Let `n_1, …, n_k ≥ 2` be multiplicatively independent integers, `N = n_1⋯n_k`, `Γ = Z[1/N]`,
`Λ = ⟨n_1, …, n_k⟩ ≤ Q_{>0}`, and `V = V(Γ,Λ,1)`, the right-continuous piecewise-linear bijections of
`[0,1)` with slopes in `Λ` and finitely many breakpoints in `Γ`. Put `g = gcd(n_1 − 1, …, n_k − 1)`.

1. `V = [[G_Λ]]` for the one-vertex k-graph `Λ_n` below.
2. `V` is of type `F_∞`, in particular finitely presented.
3. `V^ab` is finite, of order dividing `gcd(g,2)·g^{k−1}`. So `D(V)` is a finite-index simple group of
   type `F_∞`. If `g = 1`, for example for `V_{2,3}` and `V_{2,3,5}`, then `V` is perfect and simple.
4. `V` acts with type (A) on `Γ ∩ [0,1)`. So every subgroup of `V` satisfies permutational
   Boone–Higman, including Stein's `F_{n_1..n_k}` and `T_{n_1..n_k}`.

For `k = 1` this is Brown's `F_∞` for `V_{n,1}` and Higman's abelianization.

## The k-graph

- **Category.** `Λ_n = {(a, r) : a ∈ N^k, 0 ≤ r < n^a}` with `n^a = ∏ n_j^{a_j}`, degree `d(a,r) = a`, and
  `(a, r)(a', r') = (a + a', r·n^{a'} + r')`.
- **Geometric meaning.** `(a, r)` is the aligned interval `I(a,r) = [r/n^a, (r+1)/n^a)`, and the product
  places `I(a',r')` inside `I(a,r)` by the increasing affine map `[0,1) → I(a,r)`.
- **Unique factorization.** If `d = a + b`, then `r = r_1 n^b + r_2` with `0 ≤ r_2 < n^b` is Euclidean
  division, so `(a+b, r) = (a, r_1)(b, r_2)` uniquely. Hence `Λ_n` is a one-vertex k-graph, row-finite
  with no sources, with `|Λ^{e_j}| = n_j ≥ 2`.
- **Infinite paths.** An infinite path is fixed by its prefixes of degree `(t,…,t)`, which are nested
  base-`N` digit strings. So `Λ^∞ ≅ {0,…,N−1}^ℕ`, and the value map `π` identifies `Λ^∞` with `X`, the
  interval `[0,1]` Cantorized at `Γ ∩ (0,1)`. The cylinder of `(a,r)` is the Cantorized `I(a,r)`.
- **Bisections.** The basic bisection `Z(λ,μ)` acts as the increasing affine map `κ: I(μ) → I(λ)`, whose
  slope `n^{d(μ)−d(λ)}` lies in `Λ` and whose translation part lies in `Γ`.
- **Opposite.** With the same labels, `(a',r')(a,r) = (a + a', r + n^a r')` in the opposite category.
  That is the composition of `ct-p-z-is-a-one-vertex-k-graph-full-group` for `n = P'`. So Kohl's
  `CT_P(Z)` and Stein's `V_{P'}` are the full groups of a one-vertex k-graph and of its opposite.

## Proof

1. **Groupoid properties.** As in `ct-p-z-is-a-one-vertex-k-graph-full-group`:
   - **Effective.** If `Z(λ,μ)` acts as the identity on an open set, then `κ` has slope 1 and fixes
     a point. Slope 1 means `n^{d(μ)} = n^{d(λ)}`, hence `d(λ) = d(μ)` by independence, and then
     `I(λ) = I(μ)`, so `λ = μ`. Independence is needed: for `n = (2,4)` the paths of degrees `(2,0)`
     and `(0,1)` have the same interval, which gives isotropy with trivial germ.
   - **Minimal.** Every point lies in an aligned interval of each degree `(t,…,t)`, and `κ` maps that
     interval onto any given aligned interval.
   - **Purely infinite.** Split a target interval into sub-intervals of degree `(t,…,t)` and map `n`
     given aligned intervals into `n` of them. This is Matui's `pim` criterion, which gives comparison.
2. **`V ⊆ [[G_Λ]]`.** By Tanner's normal form, each piece of `g ∈ V` is `x ↦ μ_i x + c_i` with
   `μ_i = n^{u_i}` (`u_i ∈ Z^k`) and `c_i ∈ Γ`. Choose `s` so large that:
   - every breakpoint and every `c_i` lies in `N^{−(s − max_j |u_{i,j}|)}Z`;
   - `s ≥ max |u_{i,j}|`.

   Cut the domain into the aligned intervals `J` of degree `(s,…,s)`, each inside a piece. Let `y` be
   the left end of `J` and put `b = (s,…,s) − u_i ∈ N^k`.
   - `g(J)` has length `μ_i N^{−s} = n^{−b}`.
   - Its left end `z = μ_i y + c_i` satisfies `z·n^b = y N^s + c_i n^b ∈ Z`.

   So `g(J)` is the aligned interval of degree `b` containing `z`, and `g|_J` is the canonical `κ`. So `g`
   is piecewise `κ` on a clopen partition, which puts it in `[[G_Λ]]`.
3. **`[[G_Λ]] ⊆ V`.** An element of `[[G_Λ]]` is, on a finite clopen partition of `X` into cylinders, a
   canonical `κ`. By `π` it is a right-continuous piecewise-affine bijection of `[0,1)` with slopes in
   `Λ` and breakpoints in `Γ`.
4. **`F_∞` (item 2).**
   - Li's Cor. `cor:OneVertex` applies to the monoid of `Λ_n`, since `d^{−1}(e_j) = n_j ≥ 2`.
   - Take `X = ∂Ω` and `e_P = ∅`, so `Y = X`. Then `F(I_l ⋉ ∂Ω)` is of type `F_∞`.
   - `I_l ⋉ ∂Ω = G_Λ` (standard). So `V = [[G_Λ]]` is `F_∞`.
5. **Abelianization (item 3).**
   - FKPS Thm. `thm:H computation`: `H_n(G_Λ) ≅ (Z/g)^{binom(k−1,n)}` for `0 ≤ n ≤ k − 1`, whatever the
     factorization rules.
   - Li's AH sequence (minimal, comparison, no isolated points) gives
     `H_0(G;Z/2) → V^ab → H_1(G) → 0`, with `H_0(G;Z/2) = Z/g ⊗ Z/2` and `H_1(G) = (Z/g)^{k−1}`.
   - Matui's `simple2` makes `D([[G_Λ]])` simple. A finite-index subgroup of an `F_∞` group is `F_∞`.
   - If `g = 1`, then `V^ab = 0` and `V = D(V)` is simple.
6. **Type (A) (item 4).** This is `stein-v-groups-act-with-type-a-on-breakpoints`:
   - (F1) is item 2;
   - (F2), finite generation of `V(Γ,Λ,ℓ')` for every `ℓ' ∈ Γ ∩ (0,1)`, is Tanner's Thm. `fg v type`,
     since `Λ` is finitely generated and `Γ = Z[Λ]`.

   The subgroup of circle homeomorphisms is `T_{n_1..n_k}`, and `F_{n_1..n_k}` is the subgroup fixing
   `0`. ∎

## Remarks

- **Named consequence.** This settles `stein-group-v23-subgroups-satisfy-pbh` (route
  `stein-group-v23-pbh-via-k-graph-finiteness`). Finite presentation of `T_{2,3}` is still open.
- **BFFHZ Question 3.4.** `V_{2,3}` is a finitely presented simple group in `B_A`: its breakpoint
  action is of type (A). The same holds for every finitely presented simple subgroup of these `V`, and
  for `D(V)`.
- **Open side question.** Are `CT_P(Z)` and `V_{P'}` isomorphic? They are the full groups of opposite
  k-graphs, and FKPS gives them the same homology. By Matui's isomorphism theorem they are isomorphic iff
  the two groupoids are. For `P = ∅` both are `V`.

## Lesson for general BH

Integral slopes commute because subdividing into `n_1` and then `n_2` equal pieces is the same partition as
the reverse order. That is exactly the unique-factorization (k-graph) axiom, and Li's Garside machinery then
gives `F_∞` for free. Algebraic slopes lose this: a β-subdivision and a γ-subdivision have no common
refinement into admissible pieces. There one must fall back on a contracting coding, which carries only
one Pisot slope. So a Thompson-like host can carry several independent contraction directions only when
they are packaged as a higher-rank graph, i.e. as *commuting* renormalizations. This is the Thompson-group
form of the carrier principle: every independent scaling the input needs must be a separate, commuting
colour of the host's Garside structure.
