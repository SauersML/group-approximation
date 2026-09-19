---
rg: 2
id: s-arithmetic-affine-rn-groups-are-k-graph-full-groups-proof
kind: route
title: The maps x -> (t^m x + N)/Q with Q a product of the finite S-primes, m the S-degree and deg N < m form a one-vertex k-graph monoid whose path groupoid is the affine germ groupoid; Li gives F_infinity and a Koszul complex on (1-q, 1-q^(d_i)) gives the homology
target: s-arithmetic-affine-rn-groups-are-k-graph-full-groups
requires:
  - li-finite-k-graph-full-groups-are-f-infinity
  - finite-k-graph-boundary-groupoid-standard-facts
  - li-derived-full-group-homology-is-k-theory-cover
  - basilica-rn-group-is-not-a-k-graph-full-group
artifacts:
  - experiments/rn-lamplighter-finiteness-2026-09-17/s_arithmetic_kgraph.py
  - experiments/rn-lamplighter-finiteness-2026-09-17/results-s-arithmetic-kgraph.txt
---

Notation is as in the claim. For `e ∈ N^{k-1}`, write `Q_e = Π p_i^{e_i}`. For `n = (n_∞, e) ∈ N^k`, write
`m(n) = n_∞ + Σ e_i d_i`. Degrees `deg` are at `∞`. Every `Q_e` is a unit of `O`, since `p_i(0) ≠ 0`. Maps compose
right to left, and `xy` means `x ∘ y`.

## 1. The monoid

**Distinct symbols give distinct maps.** An element `a_{n,N}(x) = (t^{m(n)}x + N)/Q_e` of `P_n` has multiplier
`t^{m(n)}/Q_e ∈ U`. The group `U` is free abelian on `t, p_1, ..., p_{k-1}`, by unique factorisation in `F_q[t]`. So
the multiplier determines `(m(n), e)`, and hence `n`. The translation `N/Q_e` then determines `N`. So
`d : P → N^k` is well defined.

**Closure.** Take `a = a_{n,N_1}` and `b = a_{r,N_2}`, with `m_1 = m(n)` and `m_2 = m(r)`. Then
`ab(x) = (t^{m_1+m_2}x + t^{m_1}N_2 + N_1Q_{e(r)})/(Q_{e(n)}Q_{e(r)})`. Here:
- `deg(t^{m_1}N_2) < m_1 + m_2`;
- `deg(N_1Q_{e(r)}) < m_1 + Σ r_i d_i ≤ m_1 + m_2`.

So `ab = a_{n+r, N}` with `N = t^{m_1}N_2 + N_1Q_{e(r)}`, and `d(ab) = d(a) + d(b)`. The identity is `a_{0,0}`.

**Unique factorisation.** Let `a = a_{n+r,N}`. We need all `(N_1, N_2)` with `deg N_1 < m_1`, `deg N_2 < m_2` and
`N = t^{m_1}N_2 + N_1Q_{e(r)}`.
- Reducing mod `t^{m_1}` gives `N_1 ≡ N·Q_{e(r)}^{-1} (mod t^{m_1})`. The inverse exists because
  `Q_{e(r)}(0) ≠ 0`. So `N_1` is unique.
- Then `N - N_1Q_{e(r)}` is divisible by `t^{m_1}`. It has degree `< max(m_1 + m_2, m_1 + deg Q_{e(r)}) = m_1 + m_2`.
  So `N_2 = (N - N_1Q_{e(r)})/t^{m_1}` is a polynomial of degree `< m_2`.

So each `a` with `d(a) = n + r` factors uniquely as `a = xy` with `d(x) = n` and `d(y) = r`. Therefore `(P, d)` is a
one-vertex `k`-graph `Λ`.
- The edges of colour `∞` are `x ↦ tx + c` with `c ∈ F_q`, so there are `q` of them.
- The edges of colour `p_i` are `x ↦ (t^{d_i}x + c)/p_i` with `deg c < d_i`, so there are `q^{d_i}` of them.

(Part B of the script checks the bijections `E_i × E_j → P_{ε_i+ε_j}`. Part C brute-forces uniqueness for
`n, r ∈ {0,1}^k` and runs the solver above on random larger cases.)

**Balls.** `a_{n,N}(O) = N/Q_e + t^{m(n)}O`, because `Q_e` is a unit. Multiplication by the unit `Q_e^{-1}` is a
bijection of `F_q[t]/t^m`. So `{a(O) : a ∈ P_n}` is the set of all `q^{m(n)}` balls of radius `|t|^{m(n)}` in `O`,
each hit once (script part A).

## 2. The path space

An infinite path of the one-vertex `k`-graph is a family `(x(0,n))_{n ∈ N^k}` in `P` with `d(x(0,n)) = n`, such
that `x(0,n)` is a prefix of `x(0,n')` for `n ≤ n'`.
- **The map.** The balls `x(0,n)(O)` are nested, with radii `|t|^{m(n)} → 0`. Let `π(x)` be their intersection
  point.
- **Surjective and injective.** Given `ω ∈ O`, let `a_n` be the unique element of `P_n` with `ω ∈ a_n(O)` (§1,
  Balls). For `n ≤ n'`, factor `a_{n'} = xy` with `d(x) = n`. Then `ω ∈ x(O)`, so `x = a_n`. So `(a_n)` is a path
  with `π = ω`, and it is the only one.
- **Homeomorphism.** `π(Z(λ)) = λ(O)`. Cylinders and balls are bases, and both spaces are compact Hausdorff, so
  `π : Λ^∞ → O` is a homeomorphism.
- **Shift.** For every `p`, `π(x) = x(0,p)(π(σ^p x))`.

From now on `Λ^∞` is identified with `O`.

## 3. Aff(R, U) germs and V_q(H)

**Lemma D.** Let `g(x) = ux + b` be in `Aff(R, U)`. Write `u = t^{a_0} Π p_i^{a_i}` and
`b = B/(t^{c_0} Π p_i^{c_i})`, with `B ∈ F_q[t]` and `c_i ≥ 0`. Put `σ = Σ a_i d_i`, and let
`M_0(g) = max(0, max_i(a_i + c_i), -a_0 - σ, deg B - c_0 - Σ c_i d_i - a_0 - σ + 1)`.
Let `M ≥ M_0(g)` and `μ = a_{(M,...,M),N} ∈ P`. If `gμ(O) ⊆ O`, then `gμ ∈ P`.

*Proof.* Let `m = M(1 + Σ d_i)` and `Q = Π p_i^M`. Then `gμ(x) = (ut^m/Q)x + (uN/Q + b)`.
- **Degree.** Put `n'_i = M - a_i ≥ 0`, `m' = m + a_0` and `n'_∞ = m' - Σ n'_i d_i = M + a_0 + σ ≥ 0`. Then
  `ut^m/Q = t^{m'}/Q_{n'}`.
- **Numerator.** The translation is `c = N'/Q_{n'}`, with
  `N' = t^{a_0}N + t^{-c_0} B Π p_i^{M - a_i - c_i} ∈ F_q[t, 1/t]`.
- **Polynomial.** `gμ(O) ⊆ O` gives `c = gμ(0) ∈ O`. So `N' = cQ_{n'} ∈ O ∩ F_q[t, 1/t] = F_q[t]`.
- **Size.** Measure at `∞`. First, `deg(uN/Q) = a_0 + σ + deg N - MΣd_i < a_0 + σ + M = n'_∞`. Second,
  `deg b = deg B - c_0 - Σ c_i d_i < n'_∞` by the choice of `M_0`. So `deg c < n'_∞`, and
  `deg N' < n'_∞ + Σ n'_i d_i = m'`.

Hence `gμ = a_{n',N'} ∈ P`. ∎ (Script part D checks this on 20,370 cases with `gμ(O) ⊆ O`, with no failure.)

**The pseudogroup.** Let `𝒫` be the pseudogroup on `O` generated by `H` and the digit maps `λ_c(x) = c + tx`.
Nekrashevych's `V_q(H)` is the group of homeomorphisms of `O` that are locally in `𝒫`, since `h λ_c = λ_{h(c)} h|_c`
reduces every element of `𝒫` locally to the form `λ_v h λ_w^{-1}`. So `V_q(H) = F(𝒢_H)`, where `𝒢_H` is the germ
groupoid of `𝒫`.
- **`𝒫 ⊆ Aff(R, U)`.** We have `H ⊂ Aff(R_0, U_0) ⊂ Aff(R, U)` and `λ_c ∈ Aff(R, U)`.
- **`P ⊆ 𝒫`.** `a_{n,N} = h ∘ λ_0^{m(n)}` with `h(y) = Q_e^{-1}y + N/Q_e ∈ H`.
- **Every germ is in `𝒫`.** Let `g ∈ Aff(R, U)` and `ω ∈ O` with `g(ω) ∈ O`. `O` is open in `K_v` and `g` is
  continuous, so there is `M ≥ M_0(g)` and `μ ∈ P_{(M,...,M)}` with `ω ∈ μ(O)` and `gμ(O) ⊆ O`. By Lemma D,
  `λ := gμ ∈ P`, and `g = λμ^{-1}` on `μ(O)`.

So `𝒢_H` is the groupoid of germs of `Aff(R, U)` at points `ω ∈ O` with `g(ω) ∈ O`.

## 4. `G_Λ ≅ 𝒢_H`

Use the path groupoid `G_Λ` with basic sets `Z(λ, μ) = {(λz, d(λ) - d(μ), μz)}`. This is Li's boundary groupoid, by
item 1 of `finite-k-graph-boundary-groupoid-standard-facts`. Define
`Φ(λz, d(λ) - d(μ), μz) = [λμ^{-1}, μ(z)]`, the germ at `μ(z)` of the affine map `λμ^{-1} : μ(O) → λ(O)`.

- **Well defined.** Suppose `(λz, n, μz) = (λ'z', n, μ'z')`, and let `y = μz` and `ℓ = d(μ) ∨ d(μ')`.
  - Write `y(0,ℓ) = μν = μ'ν'`.
  - Since `d(λ) - d(μ) = d(λ') - d(μ')`, the prefix of `x = λz` of degree `d(λ) + ℓ - d(μ)` equals both `λν`
    and `λ'ν'`.
  - So `λμ^{-1}` and `λ'μ'^{-1}` both agree with `(λν)(μν)^{-1}` on the neighbourhood `μν(O)` of `π(y)`.
- **Homomorphism.** Composable arrows can be refined to representatives of the form `(λz, κz)` and `(κz, μz)`.
  Then `(λκ^{-1})(κμ^{-1}) = λμ^{-1}` on `μ(O)`.
- **Homeomorphism onto the image.** `Φ` maps `Z(λ, μ)` bijectively onto the basic bisection of germs of `λμ^{-1}`
  over `μ(O)`. These sets are bases on both sides.
- **Injective.** Suppose two arrows with the same source have the same germ. Two affine maps that agree on an
  open set are equal, so the multipliers `t^{m(λ)-m(μ)} Q_{e(μ)}/Q_{e(λ)}` agree. Since `U` is free on
  `t, p_i`, this fixes `m(λ) - m(μ)` and `e(λ) - e(μ)`, and hence `d(λ) - d(μ)`, because `n ↦ (m(n), e)` is
  injective. The ranges agree too. An arrow of `G_Λ` is determined by its range, degree and source.
- **Surjective.** This is the last bullet of §3: `[g, ω] = [λμ^{-1}, ω] = Φ(λz, d(λ) - d(μ), μz)`, where
  `ω = μ(z)`.

So `Φ : G_Λ → 𝒢_H` is an isomorphism of topological groupoids, and `V_q(H) = F(𝒢_H) ≅ F(G_Λ)`.
- **Effective.** A non-identity affine map fixes at most one point, so no open bisection of non-units lies in the
  isotropy.
- **Cantor.** `O` is a Cantor set.

## 5. Type `F_∞`

`Λ` is finite with one vertex. It has `q ≥ 2` loops of colour `∞`, and `q^{d_i} ≥ 2` loops of colour `p_i`. By
`li-finite-k-graph-full-groups-are-f-infinity`, with `X = ∂Ω`, `Y = ∂Ω` and item 1 of the standard facts,
`F(G_Λ)` is of type `F_∞`. So `V_q(H)` is of type `F_∞`. ∎

## 6. Homology

By Farsi–Kumjian–Pask–Sims (arXiv:1808.07807; recalled in `finite-k-graph-boundary-groupoid-standard-facts`, and
used the same way in `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof` §4), `H_*(G_Λ)` is the homology
of `⊗_j (Z --(1 - M_j^t)--> Z)`. For one vertex this is the Koszul complex `K(a)` of `a = (a_∞, a_1, ..., a_{k-1})`,
with `a_∞ = 1 - q` and `a_i = 1 - q^{d_i}`.

- **Change of basis.** `K(a)` is `Λ^*(Z^k)` with contraction by `a` as differential. For `γ ∈ GL_k(Z)`,
  `Λ^*(γ)` is an isomorphism `K(a) ≅ K(aγ^{-1})`.
- **Reduction.** `q - 1` divides every `q^{d_i} - 1`, so subtracting `((q^{d_i} - 1)/(q - 1))` times the first
  coordinate turns `a` into `(1 - q, 0, ..., 0)`.
- **Tensor splitting.** `K(1 - q, 0, ..., 0) = K(1 - q) ⊗ Λ^*(Z^{k-1})`, and the second factor has zero
  differential. `K(1 - q)` is `Z --(1-q)--> Z`, with `H_0 = Z/(q-1)` and `H_1 = 0`.
- **Result.** `H_j(𝒢_H) ≅ (Z/(q-1))^{C(k-1, j)}` for `j ≤ k - 1`, and `0` otherwise. Script part E computes Smith
  forms directly, for five configurations with `k ≤ 4`, and they agree.

This is consistent with the necessary condition of `basilica-rn-group-is-not-a-k-graph-full-group` (part 2):
`H_*(𝒢_H; Q) = 0`.

## 7. Acyclicity, simplicity, abelianisation

The hypotheses of Li's Corollary D (arXiv:2209.08087; `li-derived-full-group-homology-is-k-theory-cover` item 2)
are checked as in `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof` §5.
- **Ample, Hausdorff, effective, with Cantor unit space.** This is §4.
- **Minimal.** The orbit of `ω` contains `λ(ω)` for every `λ ∈ P`, and so meets every ball.
- **Comparison.** There is no invariant probability measure, since `μ(O) = Σ_c μ(λ_c O) = qμ(O)`. Every nonempty
  compact open `V` contains some `μ(O)` with `μ ∈ P`, and the bisection `μ` carries any compact open `U ⊆ O` into
  it.

The conclusions:
- **`q = 2`.** `H_*(𝒢_H) = 0`, so `F(𝒢_H) = D(𝒢_H)` is integrally acyclic. `D(𝒢_H)` is simple (Matui;
  Nekrashevych), so `V_2(H)` is acyclic, perfect and simple.
- **General `q`.** `H_*(𝒢_H; Q) = 0`, so `D(𝒢_H)` is rationally acyclic (Corollary C). By Corollary E,
  `H_1(V_q(H)) → H_1(𝒢_H) ≅ (Z/(q-1))^{k-1}` is onto.

## 8. Non-contraction and special cases

- **Not contracting for `k ≥ 2`.** Every section of `h(x) = ux + b` has the same multiplier `u`: if `x = c + ty`,
  then `h(x) = (uc + b) + tuy`. Suppose `H` were contracting, with nucleus `𝒩`. Then for each `n`, the sections
  of `h^n(x) = p_1^n x` at deep enough levels would lie in `𝒩`, with multiplier `p_1^n`. These multipliers are
  pairwise distinct, so `𝒩` would be infinite, which is a contradiction.
- **`k = 1`.** `H = F_q[t]` acts by translations. Adding `b` changes only the first `deg b + 1` digits, because
  there are no carries. So `H` is finitary and `V_q(H) = V_q`. The graph `Λ` is the `q`-rose, as expected.
- **`k = 2`, `p_1 = t - a`.** Substituting `t ↦ t + a` identifies `(R, U, O)` with the data of
  `rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph` §6. That recovers the lamplighter.

## 9. Number fields (SKETCH)

Let `K` be a global field and `v` a finite place, with local ring `O_v`, uniformiser `π` and residue field of size
`N(v)`. Let `S ∋ v` contain the archimedean places and at least one other place, and let `U ≤ O_S^×` be torsion-free
with `|U|_v ≠ 1`. Put `𝒢 = (Aff(O_S, U) ⋉ K_v)|_{O_v}`.

**Step 1 (Morita).** `O_S` is dense in `K_v`, by strong approximation. So `O_v` meets every orbit, and
`H_*(𝒢; Q) = H_*(Aff(O_S, U); C_c(K_v, Q))`. This is the first computation of
`rn-lamplighter-is-f-infinity-and-acyclic-via-a-2-graph-proof` §4.

**Step 2 (translations).** Let `L_n = O_S ∩ π^n O_v`.
- By Shapiro and colimits, `H_p(O_S; C_c(K_v, Q)) = colim_n H_p(L_n; Q)`, where the maps are the transfers.
- Every `L_n` is torsion-free with `L_n ⊗ Q = K` (number field) or is `p`-torsion (function field). So
  `H_p(L_n; Q) = Λ^p_Q(K)` or `Q·[p = 0]`, and inclusion is an isomorphism on rational homology.
- The transfer is `N(v)` times the inverse of inclusion. So the colimit is `Λ^p_Q(K)` (resp. `Q` in degree 0),
  normalised by Haar measure.
- `u ∈ U` acts by `|u|_v · Λ^p(m_u)`, where `m_u` is multiplication by `u` on `K`.

**Step 3 (units).** Over `C`, `K ⊗ C = ⊕_σ C_σ`, and `m_u` acts on `C_σ` by `σ(u)`. So `Λ^p` is a sum of the
characters `χ_I(u) = |u|_v Π_{σ ∈ I} σ(u)`, with `|I| = p`. `U ≅ Z^r` acts semisimply, and
`H_*(Z^r; C_χ) = 0` for `χ ≠ 1`. So the Lyndon–Hochschild–Serre spectral sequence is zero at `E^2`, unless some
`χ_I` is trivial on `U`.

If some `χ_I` is trivial, take `b = |I|` minimal. Then `E^2_{0,b} ≠ 0`, and every row below `b` is zero. Every
differential into or out of `(0, b)` has a zero source or target, so `H_b(𝒢; Q) ≠ 0`.

**Function fields.** Only `p = 0` occurs, with `χ_∅(u) = |u|_v ≠ 1`, so the groupoid is always rationally acyclic.
This agrees with §6.

**Examples** (script part F):
- **Odometer.** `K = Q`, `v = p`, `U = ⟨p⟩`: `χ_{id}(p) = p^{-1} · p = 1`, so `H_1 ≠ 0`. This is the obstruction
  of `basilica-rn-group-is-not-a-k-graph-full-group`.
- **Rationally acyclic.** For `U = ⟨2, 3⟩` at `v = 2`, `U = ⟨3, 2⟩` at `v = 3`, and `Q(√2)` with
  `U = ⟨√2, 1 + √2⟩` at `v = (√2)`, no `χ_I` is trivial.

**BS(1,3), integrally.** Take `v = 2`, `O_S = Z[1/6]` and `U = ⟨2, 3⟩`. By the method of Step 2 over `Z`:
- `H_0(O_S; C_c(Q_2)) = colim(Z --2--> Z --2--> ...) = Z[1/2]`, on which `2` acts by `2^{-1}` and `3` acts by `1`.
- `H_1(O_S; C_c(Q_2)) = colim(L_n, x ↦ 2x) ≅ Z[1/3]`, on which `2` acts by `1` and `3` acts by `3`. The groups
  `H_{≥2}` vanish, because `L_n` has rank one.
- Over `U`, the Koszul complex on `(1 - 2^{-1}, 0)` over `Z[1/2]` is exact. The one on `(0, 1 - 3)` over `Z[1/3]`
  gives `Z/2` in degrees `0` and `1`.
- Row `0` vanishes, so `H_1(𝒢) = Z/2`, `H_2(𝒢) = Z/2`, and `H_{≥3} = 0`.

A finite graph (`k = 1`) groupoid has `H_{≥2} = 0` and free `H_1`. So by part 1 of
`basilica-rn-group-is-not-a-k-graph-full-group`, `F(𝒢)` is not the full group of a finite graph with (H). `F(𝒢)`
is expected to be `V_2(BS(1,3))`, via the analogue of Lemma D; that was not checked here. Whether `𝒢` is a
`k`-graph groupoid for some `k ≥ 2` is open. Heuristically, the tile construction of §1 does not transfer. It
used a compact tile `O` with `uO` tiled by translates of `O` for every `u` in a generating monoid. For
`U = ⟨2, 2/3⟩` acting on `Q_3 × R`, no such tile was found; this is not proved.

**Tier.** Sketch. Steps 2–3 are argued but not written in full, and the BS(1,3) computation is not machine-checked.

## 10. Remarks

- **Torsion multipliers.** If `ζ ∈ F_q^* ∖ {1}` is allowed, `x ↦ ζx` has a torsion germ at the fixed point `0`
  that is not the identity near `0`. By `torsion-germ-rn-groups-are-not-k-graph-full-groups`, no `k`-graph model
  exists then. So the torsion-free `U` of the claim is forced, not a convenience.
- **Higher genus.** §1 used two facts about `P^1`:
  - `t` and the `p_i` generate the `S`-units freely;
  - the level sets are simply transitive, because `H^0` and `H^1` of `O(-1)` vanish.
  For a curve of genus `g`, the analogue needs each `w - (deg w)v` (`w ∈ S'`) principal, and a divisor `E`
  supported on `S'` with `deg E = g - 1` and `ℓ(E) = 0`. This is not attempted here.
