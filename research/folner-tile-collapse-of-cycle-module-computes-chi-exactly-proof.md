---
rg: 2
id: folner-tile-collapse-of-cycle-module-computes-chi-exactly-proof
kind: route
title: Proof that the tile collapse of the Cayley-cycle model of a finite cover of a cd-2 group is exact, with quotient dimensions (chi[K:N] + beta - c, beta), and that Følner tilings therefore compute chi and cannot bound it
target: folner-tile-collapse-of-cycle-module-computes-chi-exactly
requires:
  - rf-weak-bass-defect-is-degree-two-approximation-defect
  - amenable-cd-two-bass-defect-equals-euler-characteristic
---

Notation and setting as in `folner-tile-collapse-of-cycle-module-computes-chi-exactly`. All
modules are left modules, `⊗ = ⊗_{Z[K]}`, and `|X| = [K:N]`.

## 0. Numerical input

(a) *The complex computes `H_*(N; Q)`.* The Fox resolution is
`0 → P → Z[K]^n →∂_1 Z[K] → Z → 0`, and it is projective because `cd_Z K <= 2`. As a right
`Z[K]`-module, `Q[X] = Q[N\K]` is `Q ⊗_{Z[N]} Z[K]`, so `Q[X] ⊗ M = Q ⊗_{Z[N]} M` for every
`M`. Applying this to the resolution gives `C(N)`. Since the resolution restricts to a projective
resolution of `Z` over `Z[N]`, we get `H_k(C(N)) = H_k(N; Q)` (Shapiro).

(b) *Dimensions.* `r = rank_Q(Q ⊗ P) = χ + n − 1`: apply `Q ⊗ −` to the resolution and take
the alternating sum, using `b_0 = 1`. It is finite because `b_2 < ∞`. Target item 1 gives
`dim_Q C_2(N) = r|X|`, while `dim C_1 = n|X|` and `dim C_0 = |X|`. Hence

> `b_2(N) − b_1(N) + 1 = (r − n + 1)|X| = χ|X|`. (0.1)

This recovers target item 3 for `N`, since `b_0(N) = 1`.

(c) *The cycle picture.* `Q ⊗_Z P = ker(Q[K]^n → Q[K])` because `Q` is flat over `Z`. Its
elements are the finitely supported rational 1-cycles of `Cay`, where `g e_s` is the edge
`g → gs`. The map `∂ : Q[X] ⊗ P → Q[X]^n` sends `1 ⊗ z` to `π_* z`, the pushforward of the cycle
`z` to the Schreier graph `N\Cay`, whose edges are `Ng e_s`. So `∂ ∘ ρ = π_*` on cycles.

## 1. Tiles are exactly acyclic (item 1)

Write `Cay|_T` for the disjoint union of the induced graphs `Cay|_{T_j}`; edges between
different tiles are not included. Put `E(T) = ⊔_j E(T_j)` and `Z_T = ⊕_j Z_1(Cay|_{T_j}; Q) ⊂ Q ⊗_Z P`.

*`π_*` is injective on `Q^{E(T)}`.* An edge `(t, s)` with `t ∈ T` goes to `(Nt, s)`, and
`t ↦ Nt` is injective on `T`. Hence `π` is a graph isomorphism from `Cay|_T` onto its image `Γ_T`. `Γ_T`
is a subgraph of `N\Cay` on the vertex set `πT`.

*Consequences.*
- By 0(c), `∂ ∘ ρ = π_*` on `Z_T`, and it is injective there. So `ρ|Z_T` is injective and
  `ρ(Z_T) ∩ ker ∂ = 0`.
- `A = ρ(Z_T)`, the rational span of `ρ(Z_1(Cay|_{T_j}; Z))`, has
  `dim A = dim Z_T = Σ_j (|E(T_j)| − |T_j| + c_j)`.

*Subcomplex.* `∂A = π_* Z_T ⊂ π_* Q^{E(T)}`, and the boundary of `π_* Q^{E(T)}` lies in
`Q[πT]`. So `T_*` is a subcomplex of `C(N)`. Through `π`, its degree-1 → degree-0 part is the
cellular chain complex of the graph `Γ_T ≅ Cay|_T`.

*Homology.*
- `H_2(T_*) = ker(∂|A) = 0`.
- `ker(π_* Q^{E(T)} → Q[πT]) = Z_1(Γ_T) = π_* Z_T = ∂A`, so `H_1(T_*) = 0`.
- `H_0(T_*) = H_0(Γ_T) = Q^{Σ c_j}`.

Nothing here uses the size, shape or radius of the `T_j`, or any relator length: the cycle
module contains every cycle of every tile.

## 2. Exact collapse (item 2)

The short exact sequence `0 → T_* → C(N) → C(N)/T_* → 0` gives

> `0 = H_2(T_*) → H_2(N) → H_2(C/T_*) → H_1(T_*) = 0`,

so `H_2(N; Q) ≅ H_2(C(N)/T_*)`. Further along,

> `H_1(N) → H_1(C/T_*) → H_0(T_*) = Q^{Σc_j} → H_0(N) = Q → H_0(C/T_*)`.

The map `H_1(N) → H_1(C/T_*)` is injective because `H_1(T_*) = 0`. The map
`Q^{Σc_j} → Q` sends each component class to `1`, so it is onto whenever `T ≠ ∅`. Therefore
`dim H_1(C/T_*) = b_1(N) + Σc_j − 1`.

*Dimensions.* Use `|T| = (1 − θ)|X|` and `|E(T_j)| = n|T_j| − β_j`.
- Degree 0: `|X| − |T| = θ|X|`.
- Degree 1: `n|X| − |E(T)| = n|X| − n|T| + Σβ_j = nθ|X| + Σβ_j`.
- Degree 2: `r|X| − Σ_j(|E(T_j)| − |T_j| + c_j)`. This equals
  `r|X| − (n − 1)|T| + Σβ_j − Σc_j`, which is
  `(χ + n − 1)|X| − (n − 1)(1 − θ)|X| + Σβ_j − Σc_j = χ|X| + (n − 1)θ|X| + Σβ_j − Σc_j`.

*Check.* The sequence ends with `H_0(N) → H_0(C/T_*) → 0`, and the previous map is onto, so
`H_0(C/T_*) = 0`. The Euler characteristic of `C/T_*` is `χ|X| − Σc_j`. The homology gives
`b_2(N) − (b_1(N) + Σc_j − 1)`, which is the same number by (0.1). For `θ = 0` the dimensions
are `(χ|X| + β − c, β, 0)`.

## 3. Consequences at each finite level (item 3)

Take `θ = 0` and `k = 1`.

*Bounds.* `H_2(C/T_*)` is the kernel of a map `Q^{χ|X| + β − c} → Q^β`. So
`χ|X| − c <= b_2(N) <= χ|X| + β − c`. Also `H_1(C/T_*)` is a quotient of `Q^β`, so
`b_1(N) + c − 1 <= β` by §2.

*`c <= β`.* Let `Y` be a component of `Cay|_T` with no edge `(t, s)` such that `t ∈ Y` and
`ts ∉ T`. Then `ts ∈ Y` for all `t ∈ Y` and `s ∈ S`, because `ts` is adjacent to `t`. So `Ys ⊂ Y`,
and since `Y` is finite, `Ys = Y`, which gives `Ys^{-1} = Y`. Hence `Y` is closed under right
multiplication by the group `⟨S⟩ = K`, and `Y = K`. That is impossible, because `Y` is finite
and `K` is infinite. So every component contributes at least one to `β`.

*Splitting.* By §1, `H_2(N) = ker ∂` and `A` intersect in `0`. Choose a complement `R` of
`H_2(N) ⊕ A` in `Q[X] ⊗ P`. Then

> `dim R = r|X| − b_2(N) − ((n − 1)|X| − β + c)`.

By (0.1), with `b_2(N) = χ|X| − 1 + b_1(N)`, this is `β − c + 1 − b_1(N)`. The cokernel of
`Z_1(Cay|_T; Q) → Q[X] ⊗ P = H_0(N; Q ⊗ P)` has dimension `r|X| − dim A = χ|X| + β − c`, since
the map is injective by §1.

## 4. The finite-level step is the target (item 4)

Suppose `H_2(N_i) ⊂ U_i + W_i` with `U_i = im(Q[X_i] ⊗ M)` and `dim W_i <= δ|X_i|`. The map
`H_2(N_i)/(H_2(N_i) ∩ U_i) → (U_i + W_i)/U_i` is injective, so

> `b_2(N_i) <= dim(H_2(N_i) ∩ U_i) + δ|X_i|`.

By (0.1), `b_2(N_i)/|X_i| = χ − 1/|X_i| + b_1(N_i)/|X_i|`. So under `b_1(N_i)/|X_i| → 0`,
`b_2(N_i)/|X_i| → χ`, and `χ <= λ(M) + δ`.

For amenable `K`, `λ(M) = 0` for every finitely generated `M`: this is the finite-level form in
`ultraproduct-limits-of-finite-covers-see-only-the-l2-rank`, which cites Lück approximation and
`b_2^{(2)} = 0`. It is quoted only for this sentence of item 4. Conversely, if `χ < δ` then
`b_2(N_i) <= δ|X_i|` for large `i`, and `W_i = H_2(N_i)`, `M = 0` works.

For item 5 below and for the `b_1` hypothesis here, only §3 and Weiss are used.

## 5. Følner tilings (item 5)

*Weiss.* For a nested residual chain of the amenable group `K`, there are fundamental domains
`T_i` for `N_i` that form a Følner sequence. So `β(T_i)/|X_i| → 0`, since `β(T) <= |S| |∂T|` for
the outer vertex boundary.

*Limits.* By §3, `c_i <= β_i` and `b_1(N_i) <= β_i + 1`. Both are `o(|X_i|)`. Then
`χ − 2β_i/|X_i| <= b_2(N_i)/|X_i| <= χ + β_i/|X_i|`, and the cokernel of §3 has normalized
dimension `χ + (β_i − c_i)/|X_i| → χ`. For tile families with `θ_i → 0` and
`Σβ_j/|X_i| → 0`, the same computation uses the dimensions of §2.

*Blindness.* The quotient complex `C/T_*` has the numbers of item 2, and `H_2(N)` sits in its
degree-2 term. The only term not bounded by `β` or `θ|X|` is `χ|X|`. It enters only through
`dim C_2 = r|X|` (target item 1), and it is not changed by any choice of tiles. The collapse is
lossless (§2), so it holds all the information about `H_2(N)` that `C(N)` holds. Every estimate it
yields therefore has the form `b_2(N) = χ|X| + O(Σβ_j + θ|X|)`.

To conclude `χ = 0`, one must show that the degree-2 term of `C/T_*` has dimension
`o(|X|)`, that is, `r|X| − dim A = o(|X|)`. Equivalently, `r = n − 1`, because
`dim A = (n − 1)|X| − O(β)`. With `d(P) = n − 1` for infinite amenable `K`, that is
`D(P) = r(P) − d(P) = 0`, and `D(P) = χ` by `amenable-cd-two-bass-defect-equals-euler-characteristic`
item 1. This is the target restated.

*Cell models.* Let `Y` be any presentation 2-complex for `K`, with 2-cells attached along
relators. A 2-cell of the cover `N\Ỹ` whose lift is supported in a tile has its boundary in
`Cay|_{T_j}`. It maps into `A` under the cellular map
`C_2(N\Ỹ; Q) → Q[X] ⊗ P`, 2-cell `↦ 1 ⊗ (boundary cycle)`. So tile-local relators land in `A`,
which meets `H_2(N)` in `0`. Their only effect is to shrink `A`, not `H_2(N) ⊕ R`. The
relator-depth race of `folner-transversals-kill-local-degree-two-homology` is therefore replaced
by the single number `r`.

## 6. Calibrations (item 6)

*`Z² = ⟨a, b | [a, b]⟩`.* `n = 2`, `P ≅ Z[K]` (a one-relator presentation whose relator is not a
proper power), `r = 1 = n − 1`, `χ = 0`. For `N = (LZ)²` and the box `T = [0, L)²`:
- `β = 2L`: `L` edges leave on the right and `L` on the top;
- `c = 1`;
- the quotient has dimensions `(2L − 1, 2L, 0)`.

`H_2 = Q` is the kernel of a map of rank `2L − 2`, and `dim H_1(C/T_*) = 2 = b_1 + c − 1`.

*`BS(1, m)`, `m ≠ 0`.* Here `n = 2` and `P ≅ Z[K]`. For `m ≠ 1`, `b_1 = 1` and `b_2 = 0`;
`m = 1` is `Z²`. Either way `χ = 0` and `r = 1 = n − 1`.

*A torsion-free `Ã_2`-lattice `Γ` with property (T).* It acts freely on a 2-dimensional
building, so `cd Γ = 2`. Property (T) gives `b_1(N) = 0` for every finite-index `N`, so
`χ = 1 + b_2(Γ) >= 1`, and by (0.1) `b_2(N) = χ[Γ:N] − 1`. Items 1 to 3 hold. Non-amenability
gives `β(T) >= h|X|` with `h > 0` for every transversal, a uniform isoperimetric constant of
the Cayley graph. So item 3 only brackets `b_2(N)` in `[χ|X| − β, χ|X| + β]`, which is true but
carries no information. In the amenable case the same bracket shrinks to `χ|X| + o(|X|)`. Amenability fixes the
limit at `χ`, never at `0`.

## 7. What is left

The tiling route is dead at the following step. After an exact collapse, the unbounded part of
the degree-2 quotient term is `χ|X|`, and `χ` is Swan's `r − (n − 1)`, a global rank of the
coinvariants of `P`, untouched by tiles.

A proof must bound `dim H_0(N_i; Q ⊗ P) <= (n − 1)|X_i| + o(|X_i|)` from a non-tiling input.
One candidate is structure of the cross-tile remainder `H_2(N_i) ⊕ R_i` as a subquotient over
`Q[F_i]` or over a subgroup algebra.

A counterexample needs an amenable, torsion-free, non-elementary-amenable group of cd 2 whose
finite-index subgroups all have `b_1 = 0`. Its Schreier graphs would carry at least `χ|X| − c`
classes in the cycle coinvariants that no tile sees.
