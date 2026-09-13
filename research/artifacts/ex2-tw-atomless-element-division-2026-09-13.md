# The unit divides iff some self-adjoint element has no heavy eigenvalue on the tracial boundary (2026-09-13)

Lane `ex2-tw-hilbert-cube-boundary` (EX swarm). Not reviewed.

**Outcome.**
- **Theorem D.** Let `A` be exact with strict comparison and a Bauer simplex. The unit is tracially
  divisible iff for every `ε > 0` some self-adjoint `h ∈ A` has, at every extreme trace `λ`, only
  eigenvalues of trace-multiplicity `< ε`.
  - The proof turns such an `h` into a central CDF transform whose spectral distribution is uniformly
    Lebesgue on the whole boundary.
  - Its ramps give projections of constant trace in the tracial ultrapower, and comparison of
    projections finishes.
- **Witness form (tracial eigenvalue rigidity).** A strict-comparison algebra over a Bauer simplex has
  an indivisible unit iff some `ε_0 > 0` works for every self-adjoint `h ∈ A`: some extreme trace
  `λ` makes `π_λ(h)` have an eigenprojection of trace `≥ ε_0`.
- **Corollary D.2.** Suppose `A` contains a unital `C(Y)` with `Y` zero-dimensional on which every
  extreme trace restricts to an atomless measure. Then the unit divides.

This replaces matrix units, which are rigid and noncommutative, by one self-adjoint element, and
heavy eigenvalues are non-generic. The Hilbert cube question becomes a transversality question
(Section 4).

## 0. Setting and standard facts

**(S)** `A` is unital, simple, separable, exact and non-elementary, with strict comparison of
positive elements. `T(A)` is a nonempty Bauer simplex with extreme boundary `K`. `M` is the strict
closure, and `θ: C(K) → Z(M)` is Ozawa's central embedding with (F1)–(F5) of
`research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md`.
- For `x ∈ M_sa` and `λ ∈ K`, `μ_{x,λ}` is the spectral distribution of `π_λ(x)` under `λ`, so
  `∫ p dμ_{x,λ} = λ(p(x))` for polynomials `p`. An *atom* is a point of positive `μ_{x,λ}`-mass,
  namely the trace of an eigenprojection of `π_λ(x)`.
- **(D0) Continuity.** `λ ↦ μ_{x,λ}` is weak*-continuous on `K`. For `x ∈ A`, each `λ(p(x))` is
  continuous. For `x ∈ M`, it is a uniform limit of such functions.
- **(D1) Lipschitz calculus** (standard, recalled, not re-read). Let `g` be Lipschitz with constant
  `L` and `a, b` self-adjoint. In a finite von Neumann algebra `‖g(a) − g(b)‖_2 ≤ L‖a − b‖_2`, hence
  `|λ(g(a)) − λ(g(b))| ≤ L‖a − b‖_{2,λ}`.
- **(D2) Projection comparison.** In the uniform tracial ultrapower `A^ω`, projections with
  `σ(p) ≤ σ(q)` for all limit traces `σ` satisfy `p ≾ q`
  (`strict-comparison-compares-ultrapower-projections`, reviewer PASS; its hypotheses are those of (S)
  without separability or Bauer).

## 1. Theorem D

**Theorem D.** Under (S) the following are equivalent.
- (i) For every `N` and `ε > 0` there is a c.p.c. order zero `φ: M_N → A` with `τ(1 − φ(1)) < ε` for
  all `τ ∈ T(A)`.
- (ii) For every `ε > 0` some self-adjoint contraction `h ∈ A` has all atoms of every `μ_{h,λ}`,
  `λ ∈ K`, of mass `< ε`.
- (iii) For every `ε > 0` there are a self-adjoint contraction `h ∈ A` and `η > 0` with
  `μ_{h,λ}([x − η, x + η]) < ε` for all `λ ∈ K` and `x ∈ ℝ`.
- (iv) For every `ε > 0` some `u ∈ M` with `0 ≤ u ≤ 1` has
  `sup_{λ∈K} sup_s |μ_{u,λ}([0,s]) − s| ≤ ε`.

**(i) ⟹ (ii).**
- Take `N ≥ 2/ε` and `φ` as in (i) with defect `< ε/2`. Put `e_j = φ(e_jj)` and
  `h = Σ_{j≤N} (j/N) e_j`, a positive contraction since the `e_j` are orthogonal.
- **Atom at 0.** `h` and `φ(1)` have the same support, so
  `μ_{h,λ}({0}) = 1 − d_λ(φ(1)) ≤ λ(1 − φ(1)) < ε/2`.
- **Atoms at `x > 0`.** For continuous `g` with `g(0) = 0`, (F4) applied to the order zero map `g(φ)`
  makes `λ(g(e_j))` independent of `j`. So the restrictions of `μ_{e_j,λ}` to `(0,1]` equal one
  measure `ν`, and `ν((0,1]) = d_λ(e_1) ≤ 1/N`, since the `N` equal ranks add to at most 1.
- Orthogonality gives `μ_{h,λ}({x}) = Σ_j ν({Nx/j})`. The points `Nx/j` are distinct, so this is at
  most `ν((0,1]) ≤ 1/N < ε`. ∎

**(ii) ⟹ (iii).**
- Take `h` from (ii) with bound `ε/2`, and suppose that for each `k` some `λ_k ∈ K` and `x_k` have
  `μ_{h,λ_k}([x_k − 1/k, x_k + 1/k]) ≥ ε`.
- Pass to a subsequence with `λ_k → λ` and `x_k → x`. For a fixed closed `J = [x − r, x + r]`, the
  interval `[x_k − 1/k, x_k + 1/k]` eventually lies in `J`. By (D0) and the Portmanteau inequality
  for closed sets, `μ_{h,λ}(J) ≥ ε`.
- Letting `r → 0` gives an atom of mass `≥ ε > ε/2`, a contradiction. So some `η = 1/k` works. ∎

**(iii) ⟹ (iv): the central CDF transform.**
- Let `h, η, ε` be as in (iii). Put
  `F(λ, s) = ∫ clamp((s − y)/η) dμ_{h,λ}(y)` for `λ ∈ K` and `s ∈ [−1,1]`.
- The integrand is bounded and Lipschitz in `y`, uniformly in `s`. By (D0), `F` is jointly
  continuous, and it is nondecreasing in `s`.
- **Pushforward.** Fix `λ`, and write `μ = μ_{h,λ}`, `F = F(λ, ·)` and `ν = F_*μ`. Then
  `μ((−∞, s − η]) ≤ F(s) ≤ μ((−∞, s))`. For `u ∈ [0,1]`, the set `{F ≤ u}` is an interval
  `[−1, y_u]`, all of `[−1,1]`, or empty.
  - In the first case `F(y_u) = u` by continuity, so
    `u ≤ μ((−∞, y_u]) ≤ F(y_u) + μ((y_u − η, y_u]) < u + ε`.
  - All of `[−1,1]` forces `u ≥ F(1) ≥ 1 − ε`.
  - Empty is impossible, since `F(−1) = 0`.
  - Hence `sup_u |ν([0,u]) − u| ≤ ε`.
- **Realizing `F(λ, h)` in `M`.**
  - By Stone–Weierstrass choose `G(λ, s) = Σ_m a_m(λ) p_m(s)`, with real `a_m ∈ C(K)` and polynomials
    `p_m`, and `‖G − F‖_∞ ≤ ε`.
  - Put `u = clamp(Σ_m θ(a_m) p_m(h)) ∈ M`. By (F1), `θ(a_m)` is the scalar `a_m(λ)` in the fibre at
    `λ`. So `π_λ(u) = clamp(G(λ, π_λ(h)))`, and `μ_{u,λ}` is the pushforward of `μ` along a map within
    `ε` of `F(λ, ·)`.
  - Moving mass by at most `ε` changes the distance to Lebesgue by at most `ε`. So (iv) holds with
    `2ε`. ∎

**(iv) ⟹ (i).**
- **Approximants.** Take `u_n` from (iv) with `ε_n → 0`, and positive contractions `a_n ∈ A` with
  `‖a_n − u_n‖_{2,u} ≤ ε_n` (F5). Choose `η_n → 0` with `ε_n/η_n → 0`.
- **Ramps.** For `t ∈ (0,1)`, let `g_n` be `1` on `(−∞, t − η_n/2]`, `0` on `[t + η_n/2, ∞)` and linear
  between. It is `(1/η_n)`-Lipschitz, and `g_n − g_n²` is `(3/η_n)`-Lipschitz and supported in the ramp.
- **Bounds.** For `λ ∈ K`, (iv) and (D1) give
  - `|λ(g_n(a_n)) − t| ≤ η_n + ε_n + ε_n/η_n`;
  - `λ(g_n(a_n) − g_n(a_n)²) ≤ μ_{u_n,λ}([t − η_n/2, t + η_n/2]) + 3ε_n/η_n ≤ η_n + 2ε_n + 3ε_n/η_n`.
  Integrating over the representing measures (F1) extends both bounds to every `τ ∈ T(A)`.
- **A projection of constant trace.** So `p_t := [(g_n(a_n))_n] ∈ A^ω` is a projection:
  `(g − g²)² ≤ g − g²`. And `σ(p_t) = t` for every limit trace `σ`.
- **Matrix units.** Take `t = 1/k`. Inductively, with `q_j = 1 − p_1 − … − p_j` and `p_1 = p_{1/k}`,
  `σ(q_j) = 1 − j/k ≥ σ(p_1)` for `j < k`. So (D2) gives `v_j` with `v_j*v_j = p_1` and
  `v_j v_j* ≤ q_j`. Put `p_{j+1} = v_j v_j*`.
- **The remainder vanishes.** The remainder `r = q_k` is a projection with `σ(r) = 0` for all limit
  traces. `‖r‖_{2,ω}²` is attained as `σ(r)` for the limit `σ` of near-maximizing traces, so `r = 0`.
  The `v_j` give a unital `M_k ⊂ A^ω`.
- **Lifting.** A unital `*`-homomorphism `M_k → A^ω` lifts to c.p.c. order zero maps `φ_n: M_k → A`
  (projectivity of `C_0((0,1]) ⊗ M_k`), with `lim_ω sup_τ τ(1 − φ_n(1)) ≤ lim_ω ‖1 − φ_n(1)‖_{2,u} = 0`.
  As `k` is arbitrary, (i) holds. ∎

**Witness form.** The negation of (ii) reads: there is `ε_0 > 0` such that every self-adjoint `h ∈ A`
has an extreme trace `λ` where `π_λ(h)` has an eigenprojection of trace at least `ε_0`.

**Model tests.**
- `C(K)` is not simple, and its extreme traces are point evaluations. Every self-adjoint has an
  eigenvalue of multiplicity 1 at every `λ`, and indeed no order zero `M_2` is nonzero.
- A unique-trace algebra with strict comparison has `K` a point. A diffuse self-adjoint of the II_1
  fibre lifts approximately, as in (i) ⟹ (ii), and its unit divides.

## 2. Corollary D.2: zero-dimensional diagonals

**Corollary D.2.** Assume (S). Suppose `A` contains a unital commutative C*-subalgebra `C(Y)` with `Y`
compact metrizable and zero-dimensional, and suppose every `λ ∈ K` restricts to an atomless probability
measure on `Y`. Then the unit of `A` is tracially divisible. So `A` is pure
(`bauer-strict-comparison-pure-iff-divisible-unit`). If `A` is nuclear with tracially locally finite
nuclear dimension, it is `Z`-stable (`toms-winter-bauer-tlfnd-iff-tracially-divisible-unit`).

*Proof.* `Y` embeds in the Cantor set, hence in `[0,1]`. Let `h ∈ C(Y)` be an injective continuous
real function. Then `μ_{h,λ} = h_*(λ|_{C(Y)})` is atomless for every `λ ∈ K`, and (ii) holds for every
`ε`. ∎

**Example (not checked against the literature).** Let `A = C*_r(G, Σ)` be a twisted groupoid algebra
of a minimal, principal, étale groupoid with Cantor unit space, with Cartan subalgebra `C(G^0)`.
- Traces restrict to invariant measures. Minimality makes every orbit infinite, so these measures are
  atomless.
- So with exactness, strict comparison and a Bauer simplex, the unit divides and `A` is pure.
- Whether this is already known (e.g. through dynamical comparison and almost finiteness) was not
  checked; no novelty is asserted for it.

## 3. What a Hilbert cube witness must now do

Let `K = Q` and let `A` witness `hilbert-cube-bauer-strict-comparison-indivisible-unit-exists`.
- **Rigidity.** It has tracial eigenvalue rigidity at some `ε_0`. Every self-adjoint element, for
  instance any central convex combination `Σ θ(g_i) k_i` of local diffuse elements, carries an
  `ε_0`-heavy eigenvalue somewhere on `Q`.
- **Local diffuseness exists.** At each `λ_0`, lifting a diffuse element of the II_1 fibre gives `h`
  with atoms `< ε` on a neighbourhood, by usc of atom mass. Rigidity is a failure of gluing
  commutative local data.
- **No zero-dimensional diagonal.** It has no unital `C(Y)` with `Y` zero-dimensional on which extreme
  traces are atomless, so no Cartan subalgebra of that kind.

## 4. Heuristic: rigidity needs quadratic dimension growth

Not proved.
- **The multiplicity count.** In `Herm_n`, eigenvalue multiplicity `≥ m` is a stratum of codimension
  `m² − 1` (von Neumann–Wigner). Generic self-adjoint sections of a matrix bundle `End(E)` over a
  `d`-dimensional base avoid it once `d < m² − 1`, whatever the twisting of `E`, because transversality
  is local.
- **Threshold.** Atoms of mass `ε_0` at block size `n` need `m ≈ ε_0 n`, hence `d ≳ ε_0² n²` at the
  relevant stages. A homogeneous or subhomogeneous witness therefore needs quadratic dimension growth.
  This matches in shape the subquadratic ASH exclusion recorded in
  `research/artifacts/ex-open-status-2026-09-12.md` (arXiv:2607.23817, not re-read).
- **Forcing.** Beyond the threshold, forcing high multiplicity in every section is a Thom–Porteous-type
  degeneracy statement. It must survive the averaging of connecting maps while strict comparison holds.
- **The Hilbert cube.** Over an infinite-dimensional boundary, transversality with infinite
  codimension gives no dimension count. Whether central combinations of local diffuse elements can
  always avoid heavy atoms over `Q` (a Z-set-type avoidance, if the atom strata behave like Z-sets) is
  the positive side of the Hilbert cube problem in this language.
