# Virtual kernels of right-angled Artin groups, part 2: Σ-invariants see L at infinity

Lane z1-19-raag-kernel, 2026-09-13. Target: Zaremsky, *Some open problems* (July 12, 2026),
Problem 1.19. Status: UNREVIEWED. Part 1: `zp-raag-virtual-kernels-2026-09-13-part1.md`.

Summary. If a finite-index subgroup `H` of `A_L` has a nonempty homotopical invariant
`Σ^m(H)`, then `L` is `(m−1)`-connected; with homological invariants over a ring `R`, `L` is
`(m−1)`-acyclic over `R` (Theorem 7). The proof puts a copy of `L` "at infinity" in a
direction where the character grows, and retracts the punctured cube complex onto `L`.
With Bieri--Renz and Bestvina--Brady this answers Problem 1.19 affirmatively for every `n`
(Corollary 8), and it gives a second, independent proof of part 1's Theorem 3, with a
one-sided hypothesis.

## 0. Inputs

- (BR) Geometric criterion (R. Bieri and B. Renz, Comment. Math. Helv. 63 (1988); the form
  used in K.-U. Bux and C. Gonzalez, J. London Math. Soc. 60 (1999)). Let a group `G` act
  freely and cocompactly on a contractible CW complex `X`, let `χ: G → R` be a nonzero
  character, and let `g: X → R` be continuous with `g(γ p) = g(p) + χ(γ)` and bounded
  variation on cells. Then `[χ] ∈ Σ^m(G)` iff the filtration `X_{≥r} = g^{-1}[r, ∞)` is
  essentially `(m−1)`-connected: there is `λ ≥ 0` such that for all `r` and all `k ≤ m−1`,
  every map `S^k → X_{≥r}` is null-homotopic in `X_{≥r−λ}` (for `k = 0`: any two points of
  `X_{≥r}` are joined by a path in `X_{≥r−λ}`). The homological invariant `Σ^m(G; R)` uses
  reduced homology with coefficients in `R` instead of homotopy. (Some authors use
  `g ≤ r`; that swaps `χ` and `−χ` and does not affect anything below.)
- (BRk) For `G` of type `F_m` and an epimorphism `χ: G → Z`, `ker χ` is of type `F_m` iff
  `[χ]` and `[−χ]` lie in `Σ^m(G)`; likewise `FP_m(R)` with `Σ^m(G; R)` (Bieri--Renz).
- (Op) `Σ^m(G)` and `Σ^m(G; R)` are open subsets of the character sphere (Bieri--Renz).
- (BB) The Bestvina--Brady kernel `BB_L` is of type `F_m` iff `L` is `(m−1)`-connected, and of
  type `FP_m(R)` iff `L` is `(m−1)`-acyclic over `R` (M. Bestvina and N. Brady, Invent. Math.
  129 (1997)). Only the "if" directions are used.
- CAT(0) facts: `X̃`, the universal cover of the Salvetti complex `S_L`, is a CAT(0) cube
  complex with vertex set `A_L` (edges `a — a v`), `A_L` acting on the left. The link of every
  vertex is the octahedralization `OL`: vertices `v^+`, `v^−` (`v ∈ V`), and a set of signed
  vertices spans a simplex iff the underlying vertices are distinct and span a simplex of `L`.
  For a simplex `σ` of `L` and a vertex `x`, the subcomplex `x·A_σ` is a convex flat
  isometric to `R^{|σ|}`, and `x·A_σ ∩ x·A_τ = x·A_{σ∩τ}`.

All statements recalled from the sources; exact theorem numbers still to be checked.

## 1. The retraction onto L

Fix a vertex `x ∈ X̃`. Choose `ε > 0` such that `B(x, ε)` is isometric to the `ε`-ball of the
Euclidean cone over `|OL|` (all-right spherical metric). For `p ≠ x` let `dir_x(p) ∈ |OL|` be
the initial direction of the geodesic `[x, p]`. Geodesics in a CAT(0) space depend
continuously on their endpoints, and inside `B(x, ε)` they are radial, so `dir_x` is
continuous on `X̃ ∖ {x}`. Let `forget: |OL| → |L|` be the simplicial map `v^± ↦ v`. Put

`ρ_x = forget ∘ dir_x : X̃ ∖ {x} → |L|`.

Fix signs `s: V → {+, −}`. For a simplex `σ = {v_1, …, v_k}` of `L` let
`O_σ = { x·v_1^{s(v_1) t_1} ⋯ v_k^{s(v_k) t_k} : t_i ≥ 0 }` be the closed positive orthant of the
flat `x·A_σ` in these directions (a Euclidean orthant, with the real exponents read as
coordinates of the flat). These orthants satisfy `O_σ ∩ O_τ = O_{σ∩τ}`, so their union is the
Euclidean cone over the full subcomplex `Λ^s = {v^{s(v)}}` of `OL`, and `forget: |Λ^s| → |L|`
is a simplicial isomorphism. For `R > 0` let `S_R` be the set of points of this cone at
distance `R` from `x`. The geodesic from `x` to a point of `O_σ` is a straight segment inside
the flat, so `dir_x` maps `S_R` homeomorphically onto `|Λ^s|`.

**Lemma A.** `ρ_x` restricts to a homeomorphism `S_R → |L|`. In particular, a map
`S^k → S_R` that is essential in `S_R` is not null-homotopic in `X̃ ∖ {x}`, and a cycle in
`S_R` that is nonzero in `H̃_k(S_R; R)` is not a boundary in `X̃ ∖ {x}`.

## 2. Growth along orthants

Let `H ≤ A_L` have finite index and `ψ: H → R` be a nonzero character. Put the vertex `x` at
the identity `1 ∈ A_L`. For `v ∈ V` let `N_v ≥ 1` be least with `v^{N_v} ∈ H` and put
`ψ̄(v) = ψ(v^{N_v}) / N_v`. For a simplex `σ`, `Λ_σ = A_σ ∩ H` has finite index in
`A_σ ≅ Z^{|σ|}`, and `ψ|_{Λ_σ}` extends uniquely to a linear functional `ψ̄_σ` on `A_σ ⊗ R`
with `ψ̄_σ(v) = ψ̄(v)` for `v ∈ σ`.

Let `g: X̃ → R` be continuous, `H`-equivariant (`g(h p) = g(p) + ψ(h)`), with bounded variation
on cells; for instance take any `H`-equivariant values on vertices and extend multilinearly
on cubes. There are finitely many `H`-orbits of cells, so there is `C_1` with `|g(p) − g(q)| ≤ C_1`
whenever `p, q` lie in a common cube.

**Lemma B.** There is `C` such that for every simplex `σ` and every `a ∈ A_σ`,
`|g(a) − g(1) − ψ̄_σ(a)| ≤ C`.

*Proof.* Choose a finite set `B_σ ⊂ A_σ` of coset representatives for `Λ_σ`. Write `a = λ b` with
`λ ∈ Λ_σ ⊆ H`, `b ∈ B_σ`. Then `g(a) = g(λ · b) = g(b) + ψ(λ)` and `ψ̄_σ(a) = ψ(λ) + ψ̄_σ(b)`, so the
difference equals `g(b) − g(1) − ψ̄_σ(b)`, which takes finitely many values. ∎

**Lemma C.** Suppose `ψ̄(v) ≠ 0` for every `v ∈ V`, and choose `s(v) = sign ψ̄(v)`. Put
`c = min_v |ψ̄(v)| > 0`. Then every point `p` of the cone `⋃_σ O_σ` at distance `R` from `x`
satisfies `g(p) ≥ g(1) + c R − C'` for a constant `C'` independent of `p` and `R`.

*Proof.* A vertex of `O_σ` is `a = v_1^{s_1 a_1} ⋯ v_k^{s_k a_k}` with integers `a_i ≥ 0`, and
`ψ̄_σ(a) = Σ a_i |ψ̄(v_i)| ≥ c Σ a_i ≥ c · |(a_1, …, a_k)|`. By Lemma B, `g(a) ≥ g(1) + c|a| − C`. A point
`p ∈ O_σ` at distance `R` lies in a cube of `O_σ` containing a vertex `a` with `|a| ≥ R − √k`, so
`g(p) ≥ g(1) + cR − c√(dim L + 1) − C − C_1`. ∎

## 3. The theorem

**Theorem 7.** Let `L` be a finite flag complex, `H ≤ A_L` of finite index, `m ≥ 1`, and `R` a
commutative ring. If `Σ^m(H) ≠ ∅`, then `L` is `(m−1)`-connected. If `Σ^m(H; R) ≠ ∅`, then `L` is
`(m−1)`-acyclic over `R`.

*Proof.* Step 1: a good character. By (Op), `Σ^m(H)` is open and nonempty. For each `v ∈ V` the
functional `ev_v: χ ↦ χ(v^{N_v})` on `Hom(H, R)` is nonzero: the inclusion induces
`H_1(H; Q) → H_1(A_L; Q)` sending `[v^{N_v}]` to `N_v [v] ≠ 0`, so `[v^{N_v}] ≠ 0` in `H_1(H; Q)`, and
some real character is nonzero on it. The classes killed by some `ev_v` form a finite union
of proper great subspheres, which is nowhere dense. So there is `[ψ] ∈ Σ^m(H)` with
`ψ̄(v) ≠ 0` for every `v ∈ V`.

Step 2: filtration. `H` acts freely and cocompactly on the contractible complex `X̃`. Let `g` be
as in Section 2 and let `λ` be the constant of (BR) for `ψ`.

Step 3: contradiction. Suppose `L` is not `(m−1)`-connected, and choose `k ≤ m−1` and an essential
map `f: S^k → |L|` (for `k = 0`, two points in different components). By Lemma A, `f` lifts to an
essential map `f_R: S^k → S_R` with `ρ_x ∘ f_R = f`. By Lemma C, `S_R ⊆ X_{≥r}` with
`r = g(1) + cR − C'`. By (BR), `f_R` is null-homotopic inside `X_{≥r−λ}`. Choose `R` so large that
`cR − C' − λ > 0`; then `g(1) < r − λ`, so `x = 1 ∉ X_{≥r−λ}` and the null-homotopy lies in
`X̃ ∖ {x}`. Applying `ρ_x` shows that `f` is null-homotopic in `|L|`, a contradiction.

The homological statement is the same argument with reduced cycles over `R` in place of
spheres, using the homological form of (BR) and Lemma A for cycles. ∎

Remarks.
- Only one of `[ψ]`, `[−ψ]` is needed.
- `L = ∅` does not arise: the trivial group has empty character sphere.
- The same estimate shows the familiar direction for `A_L` itself: characters of `A_L`
  with no dead vertex in `Σ^m(A_L)` force `L` to be `(m−1)`-connected, matching
  Meier--Meinert--VanWyk.

## 4. Consequences

**Corollary 8 (Problem 1.19, affirmative).** Let `L` be a finite flag complex, `n ≥ 1`, `H ≤ A_L`
of finite index, and `ψ: H → Z` an epimorphism whose kernel is of type `F_n`. Then `L` is
`(n−1)`-connected, and `BB_L = ker(A_L → Z, v ↦ 1)` is of type `F_n`. So `A_L` maps onto `Z` with a
kernel of type `F_n`.

*Proof.* `H` is of type `F` (finite `K(H,1)` `X̂`). By (BRk), `[ψ] ∈ Σ^n(H)`, so `Σ^n(H) ≠ ∅`. By
Theorem 7, `L` is `(n−1)`-connected. By (BB), `BB_L` is of type `F_n`. ∎

**Corollary 9 (FP_n over any commutative ring R).** If the kernel of `ψ` is of type `FP_n(R)`, then
`L` is `(n−1)`-acyclic over `R` and `BB_L` is of type `FP_n(R)`. This re-proves part 1's Theorem 3
without division rings, for every ring.

**Corollary 10 (the open claim of part 1).** If some finite-index subgroup of `A_L` maps onto `Z`
with finitely presented kernel, then `L` is simply connected. This is Theorem 7 with `m = 2`.

## 5. Model tests

- `L` two points, `A_L = F_2`: Theorem 7 says `Σ^1(H) = ∅` for every finite-index `H`. True, since `H`
  is free of rank at least 2.
- `L` a 4-cycle, `A_L = F_2 × F_2`: Theorem 7 says `Σ^2(H) = ∅`. For `H = F_2 × F_2` itself this is the
  Stallings--Bieri phenomenon: characters nonzero on both factors have finitely generated but not
  finitely presented kernels, and characters vanishing on a factor are not even in `Σ^1`.
- `L` a flag triangulation of `RP^2`: `Σ^2(H; Z) = ∅` and `Σ^2(H) = ∅` for all finite-index `H`, while
  `Σ^m(A_L; Q) ∋ [χ_1]` for all `m`. Consistent with Bestvina--Brady.
- `L` contractible, e.g. a cone: `Σ^m(A_L) ≠ ∅` for all `m` (a cone vertex splits off a `Z` factor
  with `F`-type kernel). Consistent.

## 6. Scope and what to check

- The review should re-check: continuity of `dir_x`; the orthant cone and `S_R ≅ |L|`; Lemma B's
  uniformity; the form of (BR) with continuous equivariant heights on subspaces (it is usually
  stated with the maximal subcomplex on vertices with `g ≥ r`; the two filtrations are
  interleaved by a bounded shift, which changes only `λ`); and openness (Op).
- Novelty is unchecked (no web search budget and arXiv API 429 on 2026-09-13). The argument is
  short, so a check for an existing proof, or a known obstruction to the list's conjecture,
  must come before any claim of a first answer.
