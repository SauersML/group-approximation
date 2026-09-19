---
rg: 2
id: spectrally-complete-tuples-bound-commutative-rank-proof
kind: route
title: Cayley–Hamilton on the finite joint eigenspaces gives a spectral curve that kills the commutant, and a Vandermonde count makes band eigenfunctions locally complete
target: spectrally-complete-tuples-bound-commutative-rank
requires: []
---

Notation as in the claim. Everything happens in `A ⊗ K̄` acting on `V = K̄^Ξ`.
A `K̄`-algebra map `K[y_1, …, y_r] → A` is injective iff its extension
`K̄[y] → A ⊗ K̄` is injective, because `K̄` is flat over `K`. So we may prove every
relation over `K̄`. For `a ∈ A` write `a` for `π(a)`.

## Theorem B

**B0. The commutant preserves `W_μ`.** If `P` commutes with every `L_i` and `ψ ∈ W_μ`,
then `(L_i − μ_i) P ψ = P (L_i − μ_i) ψ = 0`. So `P W_μ ⊆ W_μ`.

**B1. Local completeness is Zariski-robust.** *If `M' ⊆ M` is Zariski-dense, then (SC2)
holds with `M'` in place of `M`.*
- Let `ℓ` be a linear functional on `K̄^F`, that is, `ℓ(φ) = Σ_{ξ ∈ F} c_ξ φ(ξ)`.
- Suppose `ℓ(ψ_j(μ)|_F) = 0` for all `μ ∈ M'` and all `j`.
- Each `r_j(μ) = ℓ(ψ_j(μ)|_F)` is a rational function of `μ`, regular on `M`.
- Write `r_j = n_j / e_j` with `e_j` nonzero on `M`. Then `n_j` vanishes on the Zariski-dense
  set `M'`, so `n_j = 0`. Hence `ℓ` vanishes on all `ψ_j(μ)|_F` with `μ ∈ M`.
- By (SC2) for `M`, `ℓ = 0`.

**B2. The vanishing lemma.** *If `Q ∈ A ⊗ K̄` kills `W_μ` for all `μ` in a
Zariski-dense `M' ⊆ M`, then `Q = 0`.*
- Fix `ξ ∈ Ξ`. Row `ξ` of `π(Q)` is finitely supported, on some finite `F ⊆ Ξ`.
- So `(Qφ)(ξ) = ℓ(φ|_F)` for a functional `ℓ` on `K̄^F`.
- `ℓ` vanishes on all `ψ_j(μ)|_F`, `μ ∈ M'`, so `ℓ = 0` by B1.
- Every row of `π(Q)` is zero, and `π` is faithful, so `Q = 0`.

**B3. A rational matrix for `P`.**
- The vectors `ψ_1, …, ψ_d ∈ K̄(μ)^Ξ` are linearly independent over `K̄(μ)`: a relation
  `Σ c_j(μ) ψ_j = 0` with some `c_j ≠ 0` would specialise, at `μ ∈ M` off the zeros and poles
  of the `c_j` (a Zariski-dense set), to a nontrivial relation among the basis `ψ_j(μ)` of `W_μ`.
- So some `d × d` minor is nonzero. That is, there is a set `F_0 ⊆ Ξ` of size `d` such that
  `Ψ(μ) = (ψ_j(μ)(ξ))_{ξ ∈ F_0, j ≤ d}` has nonzero determinant `δ(μ) ∈ K̄(μ)`.
- Let `M_1 = {μ ∈ M : δ(μ) ≠ 0}`. It is Zariski-dense.
- For `μ ∈ M_1`, restriction to `F_0` is an isomorphism `W_μ → K̄^{F_0}`.
- By B0, `P ψ_j(μ) = Σ_k m_{kj}(μ) ψ_k(μ)`. Restricting to `F_0` gives
  `m(μ) = Ψ(μ)^{-1} · ((Pψ_j(μ))(ξ))_{ξ ∈ F_0, j}`.
- Row-finiteness of `P` makes each `(Pψ_j)(ξ)` a finite `K`-combination of entries of the
  `ψ_k`. So `m ∈ M_d(K̄(μ))`, regular on `M_1`, and it is the matrix of `P|W_μ` for `μ ∈ M_1`.

**B4. The spectral curve.**
- Let `χ(μ, y) = det(y · 1 − m(μ)) ∈ K̄(μ)[y]`. It is monic of degree `d` in `y`.
- Let `D(μ) ∈ K̄[μ]` be a common denominator of its coefficients, and `Φ = D · χ`.
- Then `Φ ∈ K̄[μ, y]` has `y`-degree `d` and leading coefficient `D ≠ 0`.
- Let `M_2 = {μ ∈ M_1 : D(μ) ≠ 0}`, which is Zariski-dense.
- Put `Q = Φ(L_1, …, L_s, P)`. This is well defined, since `L_1, …, L_s, P` commute.
- On `W_μ` each `L_i` acts as `μ_i`, so `Q|W_μ = Φ(μ, P|W_μ)`.
- For `μ ∈ M_2` this equals `D(μ) χ(μ, P|W_μ) = 0` by Cayley–Hamilton.
- By B2, `Q = 0`. This proves Theorem B.1.

**B5. Non-zero-divisors.** Let `0 ≠ g ∈ K̄[μ]`, and let `Z` commute with the `L_i`.
- Suppose `g(L) Z = 0`. On `W_μ`, which `Z` preserves by B0, this reads `g(μ) Z|W_μ = 0`.
- So `Z` kills `W_μ` for `μ` in the Zariski-dense set `{μ ∈ M : g(μ) ≠ 0}`.
- By B2, `Z = 0`. This proves Theorem B.2, and `Z g(L) = g(L) Z` gives the other side.

*Faithfulness over `K̄`.* Let `RF(K)` be the row-finite `Ξ × Ξ` matrices over `K`. The map
`RF(K) ⊗ K̄ → RF(K̄)` is injective: write an element as `Σ_i a_i ⊗ λ_i` with the `λ_i`
`K`-independent, and read off each entry. Since `K̄` is flat over `K`, `π ⊗ K̄` is injective.
This is what B2 uses.

**B6. No polynomial ring of rank `s + 1`.** Let `C` be commutative with `L_i ∈ C`, and suppose
`K[x_1, …, x_{s+1}] ⊆ C`.
- Let `S = K̄[L_1, …, L_s, x_1, …, x_{s+1}] ⊆ C ⊗ K̄`. It is a finitely generated commutative
  `K̄`-algebra, hence Noetherian, and it contains `R = K̄[x_1, …, x_{s+1}]` (flatness).
- Let `T = R ∖ {0}`. No element of `T` is `0` in `S`, so `S_T ≠ 0`.
- Choose a minimal prime of `S_T`. It contracts to a prime `𝔭` of `S` with `𝔭 ∩ T = ∅`, and
  `𝔭` is minimal in `S`, since any smaller prime is also disjoint from `T`.
- So `R ↪ S/𝔭`, and the domain `S/𝔭` has transcendence degree `≥ s + 1` over `K̄`.
- By B.1 each `x_j` satisfies `Φ_j(L, x_j) = 0`, with leading coefficient `D_j(L)`.
- In a Noetherian ring every element of a minimal prime is a zero-divisor.
- `D_j(L)` is a non-zero-divisor on the commutant (B5), and `S` lies in the commutant. So
  `D_j(L) ∉ 𝔭`.
- So in `S/𝔭` the image of `x_j` is a root of a polynomial over `K̄[L̄]` with nonzero leading
  coefficient. It is therefore algebraic over `K̄(L̄_1, …, L̄_s)`.
- Hence `S/𝔭` has transcendence degree `≤ s`. This is a contradiction.

A domain of transcendence degree `s + 1` contains `s + 1` algebraically independent
elements, that is, a polynomial ring. `K[Z^{s+1}]` contains `K[x_1, …, x_{s+1}]`.
This proves Theorem B.3. ∎

## Theorem A

**A0. Orbit representation.** Use the convention `u f u^{-1} = f ∘ T^{-1}`. Fix `x ∈ X` and
`Ξ = Z`. Let `(fψ)(i) = f(T^i x) ψ(i)` and `(uψ)(i) = ψ(i − 1)`.
- Check: `(u f ψ)(i) = f(T^{i−1} x) ψ(i − 1) = ((f ∘ T^{-1}) u ψ)(i)`. So this is a
  representation, and it is by row-finite (banded) matrices.
- `L = Σ_k a_k u^k` acts by `(Lψ)(i) = Σ_k a_k(T^i x) ψ(i − k)`. So `L δ_j (i) = a_{i−j}(T^i x)`.
- If `π(L) = 0`, then every `a_k` vanishes on the orbit of `x`. That orbit is dense, by
  minimality, and `a_k` is continuous, so `a_k = 0`. So `π` is faithful.

**A1. The recurrence.** Let `p' = min(p, 0)`, `q' = max(q, 0)` and `d = q' − p' ≥ 1`.
- `L − μ` has offsets in `[p', q']`.
- Its coefficient at `q'` is: `a_q` if `q > 0`; `a_0 − μ` if `q = 0`; `−μ` if `q < 0`.
  The coefficient at `p'` is described the same way.
- `a_0` takes finitely many values, since it is locally constant on a compact space. Let
  `M = K̄ ∖ ({0} ∪ a_0(X))`. This is cofinite, hence Zariski-dense.
- For `μ ∈ M`, both extreme coefficient functions `c_{q'}(μ), c_{p'}(μ)` are nonzero at every
  point of `X`. For `c_{q'}` this uses nondegeneracy when `q > 0`, and `μ ∉ a_0(X) ∪ {0}`
  otherwise.
- Row `i` of `(L − μ)ψ = 0` reads
  `Σ_{k=p'}^{q'} c_k(μ)(T^i x) ψ(i − k) = 0`.
  It involves exactly the window `ψ(i − q'), …, ψ(i − p')`, of length `d + 1`.
- Both end coefficients are nonzero, so the row can be solved for `ψ(i − q')`, or for
  `ψ(i − p')`, in terms of the other `d` values.

**A2. (SC1).** Let `ψ_j` be the solution whose values on the window `[0, d)` are `δ_{·,j}`.
- It is obtained by solving A1 rightward and leftward. Each step divides by a value of
  `c_{q'}(μ)` or `c_{p'}(μ)`: an element of `K^×`, or `a_0(T^i x) − μ`, or `−μ`.
- So every entry of `ψ_j` lies in `K(μ)`, with poles only in `{0} ∪ a_0(X)`, hence none on `M`.
- For `μ ∈ M`, a solution is determined by its values on any `d` consecutive sites, and any
  such values extend. So `ψ_1(μ), …, ψ_d(μ)` is a basis of `W_μ = ker(L − μ)`.

**A3. (SC2), by Vandermonde.** It suffices to treat a window `I = [α, β]` of length
`D·d` for some `D ≥ 1`, since every finite `F` lies in such a window.
- Pick distinct `μ_1, …, μ_D ∈ M`. Suppose `φ_t ∈ W_{μ_t}` and `Σ_t φ_t = 0` on `I`.
- `(Lφ)(i)` depends on `φ` on `[i − q', i − p']`. So applying `L^r` gives
  `Σ_t μ_t^r φ_t = 0` on `I_r = [α + r q', β + r p']`, of length `D d − r d`.
- For `r = 0, …, D − 1` these hold on `I_{D−1}`, of length `d`.
- The Vandermonde matrix `(μ_t^r)` is invertible, so each `φ_t = 0` on `I_{D−1}`.
  Then `φ_t = 0` everywhere, by A2.
- So restriction to `I` is injective on `W_{μ_1} ⊕ ⋯ ⊕ W_{μ_D}`, a space of dimension
  `D d = |I|`. Its image is all of `K̄^I`, and it is spanned by the `ψ_j(μ_t)|_I`.

So `(L)` is spectrally complete, and Theorem B applies with `s = 1`.
- `L` itself is transcendental over `K`, since `W_μ ≠ 0` for every `μ ∈ M`.
- Hence a commutative subalgebra containing `L` contains no `K[x, y]`.
- *Corollary.* If `ι : F_2[Z^2] ↪ A` and some nonscalar `z ∈ ι(F_2[Z^2])` were nondegenerate,
  Theorem B.3 applied to `C = ι(F_2[Z^2])` would contradict `F_2[x, y] ⊆ C`.
∎

## Theorem C

**C0. Setup.** Use the orbit representation on `K^{Z^s}`, with `(fψ)(h) = f(h · ω) ψ(h)` and
`(u_g ψ)(h) = ψ(h − g)`. It is faithful because the orbit is dense and free. Also:
- Let `Λ = ⊕ Z v_i`, of finite index `N`. Each `L_i` maps functions on a coset `c + Λ` to
  functions on `c + Λ`. So `W_μ = ⊕_{c ∈ Z^s/Λ} W_μ^{(c)}`, and it suffices to work on one
  coset. There the coordinates are `c + Σ n_i v_i ↔ n ∈ Z^s`.
- In these coordinates `L_i` is a one-dimensional band operator along the `i`-th axis. Its
  coefficients depend on the site, and on each axis line it satisfies A1 with `d_i`, `M_i`.
  Here `M_i` avoids `0` and the finitely many values of `a_{i,0}`.
- Let `M = M_1 × ⋯ × M_s`, a Zariski-dense set, and `B = ∏ [0, d_i)`, the box.

**C1. (SC1): box data determine joint eigenfunctions.** Fix `μ ∈ M`. For `0 ≤ j ≤ s` let
`S_j = {n : n_{j+1}, …, n_s ∈ [0, d)}`, where the `i`-th slot uses `[0, d_i)`. So `S_0 = B`
and `S_s = Z^s`. Each `L_i` with `i ≤ j` maps functions on `S_j` to functions on `S_j`.

*Claim:* for each `j`, restriction `E_j → K̄^B` is bijective, where `E_j` is the set of
functions on `S_j` killed by `L_i − μ_i` for all `i ≤ j`. Induction on `j`; `j = 0` is trivial.
- **Step `j → j + 1`.** Take `ψ ∈ E_j`. Each axis-`(j+1)` line of `S_{j+1}` meets `S_j` in
  `d_{j+1}` consecutive sites.
- By A1 along that line, `ψ` extends uniquely to that line with `(L_{j+1} − μ_{j+1})ψ = 0`.
  This gives a unique `ψ̃` on `S_{j+1}`.
- Let `i ≤ j` and `φ = (L_i − μ_i) ψ̃`, a function on `S_{j+1}`. Then
  `(L_{j+1} − μ_{j+1}) φ = (L_i − μ_i)(L_{j+1} − μ_{j+1}) ψ̃ = 0`.
  This uses that both operators preserve functions on `S_{j+1}`, and that they commute there,
  because they commute as elements of `A` and their rows at sites of `S_{j+1}` only read
  `S_{j+1}`.
- Also `φ = 0` on `S_j`, because `ψ̃|_{S_j} = ψ ∈ E_j`.
- So on each axis-`(j+1)` line, `φ` solves the `L_{j+1}` recurrence and vanishes on
  `d_{j+1}` consecutive sites. Hence `φ = 0`, and `ψ̃ ∈ E_{j+1}`.
- Uniqueness of the extension gives injectivity. So `E_{j+1} → E_j → K̄^B` are bijections.

For `j = s` this gives `W_μ^{(c)} ≅ K̄^B`. Let `ψ_b` be the solution with box data `δ_{·,b}`.
Each step divides only by the nowhere-zero extreme coefficients of A1, so the entries of `ψ_b`
lie in `K(μ_1, …, μ_s)`, with no pole on `M`. Over all cosets, `d = N ∏ d_i`.

**C2. (SC2): tensor Vandermonde.** Take a box `I = ∏ [α_i, α_i + D_i d_i)` in coset
coordinates, and grids `G_i ⊆ M_i` of `D_i` distinct values.
- Suppose `Σ_{μ ∈ G_1 × ⋯ × G_s} φ_μ = 0` on `I`, with `φ_μ ∈ W_μ^{(c)}`.
- Applying `L_1^{r_1} ⋯ L_s^{r_s}` with `r_i < D_i` gives
  `Σ_μ μ^r φ_μ = 0` on a box of side lengths `≥ d_i`.
- The matrix `(μ^r)` is a tensor product of invertible Vandermonde matrices, so it is
  invertible. So each `φ_μ` vanishes on a translate of `B`.
- A translate of `B` determines a joint eigenfunction, by C1 applied after translation. So
  `φ_μ = 0`.
- The dimensions agree: `∏ D_i · ∏ d_i = |I|`. So the `ψ_b(μ)|_I` span `K̄^I`.

Every finite set lies in such a box, and different cosets are disjoint. So (SC2) holds, and
Theorem B applies with this `s`. For `s = 2` and `A = B_Ω`, a commutative subalgebra that
contains a commuting directional nondegenerate pair contains no `F_2[x, y, z]`, hence no
`F_2[Z^3]`. ∎

## Remarks

- **Full-group units.** Let `g ∈ [[T]]` act on the orbit `Z` with finitely many orbits
  `O_1, …, O_r`, all infinite. Then `u_g` is spectrally complete with `d = r`: the eigenvector
  on `O_ρ` is `μ^{n}` at `g^n(z_ρ)`, and exponents on each orbit are distinct. So local
  spanning is a nonvanishing Laurent polynomial. Here the eigenvalue is `μ^{-1}` and
  `M = K̄^×`. An example is `u^k`, with `r = |k|`. The point is that `C` may contain
  arbitrary non-monomial elements, which the germ arguments do not reach.
- **Where it dies.** If an extreme coefficient beyond `0` vanishes somewhere, then A1 cannot be
  solved through that site. `W_μ` can then be `0` (for `1_U u`, which is nilpotent by
  minimality) or infinite-dimensional (for `u_g` with infinitely many orbits on one line).
  In both cases (SC1) fails.
