# Block-balanced towers are trivial on every closed Bauer face (2026-09-12)

Lane `ex-tw-projection-starved-bundle` (EX swarm). Negative side of
`strict-comparison-forces-tracially-divisible-unit`: look for a hyperfinite W*-bundle whose unit
cannot be divided uniformly (`nontrivial-w-star-bundle-with-r-fibres-exists`, BBSTWW Question 3.14),
testing Toms- and Villadsen-type towers.

**Outcome.** No witness. The tested towers are excluded, and the search space is enlarged. Unreviewed.
1. **Faces (Lemma 1, Proposition 2).** A unital separable algebra with non-Bauer `T(A)` still gives
   W*-bundles. Every closed set `K` of extreme traces spans a closed Bauer face, and the uniform tracial
   completion over that face is a strictly separable continuous W*-bundle over `K` with fibres
   `π_λ(A)''`. So Poulsen-simplex algebras such as Toms's are admissible sources for Question 3.14.
2. **Theorem A.** Suppose `A` has *central halving* (CH): positive contractions `p_n` that are
   asymptotically central and idempotent in `‖·‖_{2,T(A)}`, with `τ(p_n) → 1/2` uniformly on `T(A)`.
   Then every such face bundle with `R` fibres is trivial. In particular the unit is tracially divisible
   relative to every closed set of extreme traces. CH asks nothing about `τ(a p_n)`.
3. **Proposition B.** Towers whose connecting maps split into many orthogonal blocks of equal constant
   rank have CH with exact projections. This covers:
   - Toms's no-Γ algebra `B` (arXiv:2606.12188v2) and its non-simple tower;
   - the DHTW algebra (arXiv:0712.2020) and the Hirshberg–Rørdam–Winter products;
   - Villadsen first-type algebras and all their corners.
4. **Corollary C.** `B` has CH but not uniform property Γ. Its Γ failure is invisible over every closed
   set of extreme traces, so no face of `B` answers Question 3.14.
5. **Corollary D (calibration).** A Hopf-seeded doubling tower `A` has no nonzero `*`-homomorphism
   `M_2 → A`, since coordinate Euler mass kills every square subbundle at every stage. Yet its unit is
   tracially `N`-divisible, for every `N`, relative to every closed set of extreme traces. Compact
   invariants (coordinate Euler, DHTW's unit rigidity) do not survive into face bundles.

## Sources read (MSI text copies under `/projects/standard/hsiehph/sauer354/lit/`)

- **Ozawa, arXiv:1304.3523** (`tw-bundle-hunter/1304.3523.txt`).
  - Line 114: `S ⊂ T(A)` is "a non-empty metrizable closed face".
  - Lines 159–165, Theorem 3: "... Moreover, if ∂S is closed, then for every τ ∈ ∂S, one has
    π_τ(A^st) = π_τ(N) = π_τ(A)''."
  - Lines 766–770: "The strict completion A^st studied in Section 4 is a continuous quasi-W*-bundle over
    S, and by Theorem 3, it is a continuous W*-bundle over ∂S if ∂S is closed in S. Conversely, if each
    fiber π_λ(M) is a factor, then K can be viewed as a closed subset of the extreme boundary of T(M)
    and hence the closed convex hull S of K is a metrizable closed face of T(M) such that ∂S = K."
  - Lines 1053–1085, Theorem 15 and its proof. For (ii) ⟹ (iii): "since π_λ(M)'s are all factors, the
    central sequence (p_n) satisfies ‖E(p_n a) − E(p_n)E(a)‖ → 0 for every a ∈ M". So balancing is
    derived, not assumed.
  - Intro: `A^u` "coincides with the closure A^st of A in N with respect to the strict topology".
- **CETW, arXiv:1912.04207** (`toms-winter/1912.04207.txt`).
  - Lines 1538–1625: Definition 5.9 and Proposition 5.10. Diagonal AH algebras
    `lim M_{n_i} ⊗ C(X_i)` with `n_i → ∞` "have uniform property Γ whenever T(A) is a Bauer simplex".
    The proof takes `p_i` as half of the diagonal blocks, "a projection in A that commutes with the
    image of μ_i", and uses Proposition 3.1 on Bauer simplices.
  - Lines 654–665, Proposition 3.1: central sequences factorize, uniformly on compact
    `K ⊆ ∂_e T(A)`.
- **Toms, arXiv:2606.12188v2** (`toms-winter/`).
  - Lines 331–441: the Section 4 tower, with `ϕ_i(a) = (π_1*a ⊗ γ_{i,1}) ⊕ (π_2*a ⊗ γ_{i,2})`,
    `ϕ_i(q_i) = q_{i+1}` and `rank(q_{i+1}) = 2d_i = d_{i+1}`.
  - Lines 1255–1300: the simple `B`, with `ψ_i = ψ_i^top ⊕ ψ_i^pt`. Here `ψ^top` is "this telescoped
    topological diagonal map applied to the whole s_i-corner", and `ψ^pt` is "the direct sum of the
    required point evaluations, placed in orthogonal summands of the new unit".
  - Lines 955–975: Section 6 certifies failure of Γ over all of `T(A)`.
- **DHTW, arXiv:0712.2020**, read in full (204 lines). `D_i = ⊗_{j≤i} B_j`, and
  `φ_i = (id ⊗ e_{i+1}) ⊕ (α_{i,[i]} ⊗ f_{i+1})`. The `B_j` are corners
  `(e_j ⊕ f_j)(C(X_j) ⊗ K)(e_j ⊕ f_j)` with rank-one `e_j, f_j`.

## 0. Conventions

- `A` is unital and separable, `T(A) ≠ ∅`, and `‖a‖_{2,S} = sup_{τ∈S} τ(a*a)^{1/2}` for `S ⊆ T(A)`.
- **Relative divisibility.** For `K ⊆ T(A)`, the unit is *tracially `N`-divisible relative to `K`* if for
  every `ε > 0` there is a c.p.c. order zero `φ: M_N → A` with `λ(φ(1)) > 1 − ε` for all `λ ∈ K`.
  For `K = T(A)` this is Definition 1.1 of `research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md`.
- **(CH) central halving.** There are positive contractions `p_n ∈ A` with:
  - `‖p_n − p_n²‖_{2,T(A)} → 0`;
  - `sup_{τ∈T(A)} |τ(p_n) − 1/2| → 0`;
  - `‖[p_n, a]‖_{2,T(A)} → 0` for every `a ∈ A`.
- Uniform property Γ at `n = 2` also requires `sup_τ |τ(a p_n) − τ(a)/2| → 0` for every `a`. On a Bauer
  `T(A)` the two agree (CETW Proposition 3.1). In general they do not (Corollary C).
- **Model test for (CH).** `C([0,1])` fails it: at `δ_x`, `p_n(x)` must be near `{0,1}` and near `1/2`.
  Toms's `B` satisfies it (Proposition B).

## 1. Face bundles

**Lemma 1.** Let `K ⊆ ∂_e T(A)` be nonempty and closed, and `F = conv‾(K)`. Then `F` is a closed face of
`T(A)`, and `∂_e F = K`. So `F` is a Bauer simplex.

*Proof.*
- `T(A)` is a metrizable Choquet simplex. Every `τ ∈ T(A)` has a unique maximal representing measure
  `μ_τ`, carried by `∂_e T(A)`.
- The barycentres of `Prob(K)` form a compact convex set containing `K`, hence equal to `F`.
- **Extreme points.** By Milman's converse, `∂_e F ⊆ K̄ = K`. Also `K ⊆ ∂_e T(A) ∩ F ⊆ ∂_e F`.
- **Face.** Let `τ = tτ' + (1−t)τ''` with `τ ∈ F`, `τ', τ'' ∈ T(A)` and `0 < t < 1`.
  - Write `τ = bar(μ)` with `μ ∈ Prob(K)`. This `μ` is carried by extreme points, so it is maximal.
  - The measure `tμ_{τ'} + (1−t)μ_{τ''}` is maximal, being carried by `∂_e T(A)`, and represents `τ`.
  - By uniqueness it equals `μ`. So `μ_{τ'}` is carried by `K`, and `τ' ∈ F`. ∎

Ozawa states the same fact for bundles with factor fibres (lines 766–770).

**Proposition 2 (face bundles).** Let `K` and `F` be as in Lemma 1, and `M_K = A^{u,F}` the completion of
`A` in `‖·‖_{2,F}`. Then:
- `M_K` is a strictly separable continuous W*-bundle over `K`, with `E(x)(λ) = λ(x)`;
- its fibre at `λ` is `π_λ(A)''`, and `‖x‖_{2,u} = ‖x‖_{2,F}`.
If `A` is nuclear and has no finite-dimensional representation, every fibre is `R`.

*Proof.*
- **Bundle.** Ozawa lines 766–770, with `S = F` and `∂S = K` closed (Lemma 1), together with
  `A^u = A^st` and the fibre clause of Theorem 3. Strict separability follows since `A` is separable
  and dense.
- **Fibres.** For `λ ∈ K`, `π_λ(A)''` is an injective finite factor. A finite-dimensional factor would
  give a finite-dimensional representation of `A`. So it is a separably acting injective II_1 factor,
  hence `R` (Connes). ∎

**Lemma 3 (dictionary).** Let `K` be closed in `∂_e T(A)` with all fibres `R`. If `M_K ≅ C_σ(K,R)`, the
unit of `A` is tracially `N`-divisible relative to `K` for every `N`. Contrapositively, a relative
divisibility gap at one `N` makes `M_K` nontrivial, which answers Question 3.14.

*Proof.*
- A unital `M_N ⊂ R` gives constant sections, hence a unital `*`-homomorphism `M_N → M_K`.
- `M_K = C/J`, where:
  - `C ⊆ ℓ^∞(A)` is the algebra of bounded `‖·‖_{2,F}`-Cauchy sequences;
  - `J` is the ideal of null sequences.
- Projectivity of `C_0((0,1]) ⊗ M_N` lifts the order zero map to an order zero `ψ: M_N → C`. Its
  coordinates `ψ_m: M_N → A` are order zero.
- Since `1 − ψ(1) ∈ J`, `λ(1 − ψ_m(1)) ≤ ‖1 − ψ_m(1)‖_{2,F} → 0` uniformly in `λ ∈ K`. ∎

## 2. Theorem A

**Theorem A.** Let `A` be unital, separable and nuclear, with no finite-dimensional representation, and
suppose `A` has (CH). Then for every nonempty closed `K ⊆ ∂_e T(A)`:
- `M_K ≅ C_σ(K,R)`;
- the unit of `A` is tracially `N`-divisible relative to `K` for every `N`.

*Proof.*
- By Proposition 2, `M_K` is a strictly separable continuous W*-bundle over `K` with all fibres `R`.
- Let `p_n` witness (CH), viewed in `M_K`. Since `F ⊆ T(A)`, each seminorm `‖·‖_{2,F}` is at most
  `‖·‖_{2,T(A)}`. So:
  - `0 ≤ p_n ≤ 1` and `‖p_n − p_n²‖_{2,u} → 0`;
  - `‖E(p_n) − 1/2‖ = sup_{λ∈K} |λ(p_n) − 1/2| → 0`;
  - `‖[p_n, a]‖_{2,u} → 0` for `a ∈ A`.
- **All of `M_K`.** The unit ball of `A` is `‖·‖_{2,u}`-dense in that of `M_K`. For contractions
  `x ∈ M_K` and `a ∈ A`, `‖[p_n, x]‖_{2,u} ≤ ‖[p_n, a]‖_{2,u} + 2‖x − a‖_{2,u}`. This uses
  `‖yz‖_{2,λ} ≤ ‖y‖‖z‖_{2,λ}` and `‖zy‖_{2,λ} ≤ ‖z‖_{2,λ}‖y‖`. So `‖[p_n, x]‖_{2,u} → 0`.
- This is condition (ii) of Ozawa's Theorem 15 (`r-fibre-bundle-triviality-iff-uniform-central-halving`),
  so `M_K` is trivial.
- Lemma 3 gives the divisibility. ∎

**Remarks.**
- **Credit.** The block mechanism is CETW's (Proposition 5.10), for trivial units and Bauer `T(A)`.
  Theorem A adds two things:
  - it needs no Bauer hypothesis on `T(A)`, only on the face;
  - it replaces uniform Γ by (CH), which omits the balancing against `a`.
  The balancing is where CETW use Proposition 3.1. Over a closed set of extreme traces it comes free
  from Ozawa's Dixmier argument.
- **Where balancing fails.** Over non-closed families, the averaged limit traces of a doubling tower need
  not balance a fixed union of blocks. That is the "cheap positive fails" record on
  `stw99-problem-xx-villadsen-algebras-uniform-gamma`. Closed sets of extreme traces never see it.

## 3. Proposition B: block-balanced towers

**Setting.** Let `A = lim (A_n, φ_n)` be unital and separable, with `μ_n: A_n → A` the canonical maps.
Call the tower *block-balanced* if there are stages `m_j < n_j`, with `m_j → ∞`, and projections
`e^{(j)}_1, …, e^{(j)}_{L_j} ∈ A_{n_j}` such that:
- they are pairwise orthogonal and sum to `1`;
- each commutes with `φ_{m_j,n_j}(A_{m_j})`;
- `τ(e^{(j)}_b) = 1/L_j` for every `b` and every `τ ∈ T(A_{n_j})`;
- `L_j ≥ 2`, and `1/2 − ⌊L_j/2⌋/L_j → 0`; for example every `L_j` is even, or `L_j → ∞`.

**Proposition B.** A block-balanced tower has (CH), with projections `p_j` such that `[p_j, a] → 0` in
norm and `sup_{τ∈T(A)} |τ(p_j) − 1/2| ≤ 1/(2L_j)`.

*Proof.*
- Put `p_j = μ_{n_j}(Σ_{b ≤ ⌊L_j/2⌋} e^{(j)}_b)`, a projection.
- It commutes exactly with `μ_m(A_m)` for every `m ≤ m_j`. The union of these images is norm dense, so
  `‖[p_j, a]‖ → 0` for every `a ∈ A`.
- Every trace of `A` pulls back to `A_{n_j}`. So `τ(p_j) = ⌊L_j/2⌋/L_j`, within `1/(2L_j)` of `1/2`. ∎

**Block splittings.** Suppose `φ_{m,n} = Σ_b φ^{(b)}`, a sum of `*`-homomorphisms with pairwise orthogonal
ranges and `Σ_b φ^{(b)}(1) = 1`.
- Then `e_b = φ^{(b)}(1)` satisfies `e_b φ^{(b')}(a) = δ_{bb'} φ^{(b)}(a) = φ^{(b')}(a) e_b`, so it commutes
  with the image.
- For `A_n = q_n(C(X_n) ⊗ K)q_n`, point traces give `τ(e_b) = rank(e_b)/rank(q_n)`.
- Equal constant block ranks therefore give `1/L`.

## 4. The towers

1. **Toms's non-simple tower** (Section 4). `ϕ_i` has two blocks, `π_1*q_i ⊗ γ_{i,1}` and
   `π_2*q_i ⊗ γ_{i,2}`, each of rank `d_i`. Composites have `L = 2^{n−m}`.
2. **Toms's simple `B`** (Section 7, Proposition 4).
   - Blocks of `ψ_i^top`: pullbacks along composites of coordinate projections, tensored with line
     bundles. Each has rank `rank(s_i)`, and there are `M_i` of them, with `M_i → ∞` by telescoping.
   - Blocks of `ψ_i^pt`: point evaluations in orthogonal summands, each of rank `rank(s_i)`.
   - So `L_i = M_i + t_i`, with equal ranks.
3. **DHTW `D`, and ⊗_j B_j** (the case `α = id`). `φ_i` has two blocks, `1 ⊗ e_{i+1}` and `1 ⊗ f_{i+1}`,
   each of rank `rank(1_{D_i})`, because `α_{i,[i]}` is unital. So `L = 2^{n−m}`.
4. **Diagonal AH algebras** with `n_i → ∞`: CETW's case. Their corners also work, see item 5.
5. **Corners.** For a projection `p ∈ A_m`, the corner tower `φ_{m,n}(p) A_n φ_{m,n}(p)` inherits the
   blocks `φ^{(b)}(p)`. These have equal rank when the eigenmap blocks do. This covers the Hopf corners
   `x A x` of Villadsen first-type algebras used by `stw27-coordinate-euler-slack-obstructs-compact-dividers`.

**Corollary C (Toms's algebra).**
- `B` has (CH) but lacks uniform property Γ (`toms-ah-counterexample-to-uniform-gamma`).
- For every nonempty closed `K ⊆ ∂_e T(B)`, `M_K` is trivial.
- Toms's certificate (equal-trace projections that are not equivalent) never restricts to a closed set of
  extreme traces.
- The same holds for his non-simple tower. There, the diagonal branch traces with free labels,
  `z_{i+1} = (z_i, z_i, ℓ_i)`, form a closed set of extreme traces homeomorphic to
  `Gr(d,2d) × Π_i CP^{j_i}`. That set contains a Hilbert cube, so the bundle over it has a strongly
  infinite-dimensional base, and it is still trivial.
- Extremality: `research/artifacts/tw-doubling-poulsen-and-comparison-2026-09-12.md`, Lemma 1.
  Continuity and injectivity of `(z_1, ℓ) ↦ trace`: stage `n` depends only on `(z_1, ℓ_1, …, ℓ_{n−1})`.

**Corollary D (the Hopf doubling tower).**
- **Setting.** `X_1 = S²` and `q_1 = L`, the Hopf line. `X_{n+1} = X_n × X_n`,
  `q_{n+1} = π_1*q_n ⊕ π_2*q_n` and `φ_n(a) = π_1*a ⊕ π_2*a`. So `q_n ≅ ⊕_{c ≤ 2^{n−1}} L_c` over
  `(S²)^{2^{n−1}}`, and `A = lim q_n(C(X_n) ⊗ K)q_n`.
- **(a) No `M_2` inside `A`.** There is no nonzero `*`-homomorphism `M_2 → A`.
- **(b) Divisible over faces.** The unit is tracially `N`-divisible relative to every nonempty closed
  `K ⊆ ∂_e T(A)`, for every `N`.

*Proof.*
- **(b).** The tower is block-balanced with `L = 2^{n−m}`. It is AH, hence nuclear. `rank q_n → ∞` and
  the maps are injective, so there is no finite-dimensional representation. Apply Theorem A.
- **(a), finite stages.** Let `e ⊥ f` be MvN-equivalent projections in `A_n`, with range bundle `F`.
  - Then `q_n ≅ F ⊕ F ⊕ G`.
  - Mod 2, `c(F ⊕ F) = c(F)²`, a sum of squares of positive-degree classes, and all such squares vanish
    in `H*((S²)^M; F_2)` with `M = 2^{n−1}`. So `c(F)² = 1`, and `c(G) = c(q_n) = Π_c (1 + e_c)`.
  - Its top term `Π_c e_c ≠ 0` has complex degree `M`. So `rank G ≥ M = rank q_n`, and `F = 0`.
  - This is the `ℓ = 2`, `t_i = 1` case of the proof of
    `stw27-coordinate-euler-slack-obstructs-compact-dividers`.
- **(a), the limit.** A nonzero `*`-homomorphism `M_2 → A` is a partial isometry `v` with
  `v*v ⊥ vv* ≠ 0`.
  - `M_2` is semiprojective, so after perturbation such a `v` lies in `μ_n(A_n)` for some `n`.
  - The maps are injective, so `A_n` has nonzero orthogonal equivalent projections, contradicting the
    finite-stage step. ∎

So the unit of `A` is tracially divisible over every closed face, while no finite stage and not `A` itself
contains a nonzero copy of `M_2`. Compact finite-stage obstructions of Villadsen type say nothing about face
bundles.
