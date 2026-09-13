---
rg: 2
id: thompson-f-following-models-mean-charges-commutator-proof
kind: route
title: Counting measures of following models converge to invariant means, level sets of almost invariant measures give following models, and fixed-point masses form a character
target: thompson-f-following-models-separate-iff-mean-charges-commutator
requires:
  - thompson-f-sofic-iff-relator-system-unstable
  - thompson-f-character-simplex
artifacts:
  - research/artifacts/thompson-f-nonspatial-f-sets-2026-09-13.md
---

Notation as in the claim.
- `μ_S` is the image of the uniform probability on `S` under `π`.
- `||·||` is the `ℓ1(Ω)` norm.
- For finitely supported `μ` and `g ∈ F`, `(gμ)(ω) = μ(g^-1 ω)`.

**0. Word paths.** This is step 2 of `thompson-f-spatial-permutation-models-almost-commute-proof`, which
never uses the map to the interval.
- Each letter `a^±1, b^±1` has at most `δ|S|` bad points, so at most `|w|δ|S|` points have a bad step
  along the path of `w(A,B)`. Every other `s` has `π(w(A,B)s) = w(x_0,x_1)π(s)`.
- **Relators.** If `w(x_0,x_1) = e`, injectivity of `π` gives `d(w(A,B), 1) ≤ |w|δ`. The relators
  have lengths 10 and 14.
- **Commutator.**
  - `d(AB,BA)` is the fraction of points moved by `ABA^-1B^-1`, a word of length 4 that evaluates
    to `c`.
  - A point with a good path is moved exactly when `c` moves `π(s)`.
  - So `|d(AB,BA) - μ_S(Moved(c))| ≤ 4δ`.

**1. Means from models.**
- Let `E ⊆ Ω`. A point `s` with `x_0π(s) ∈ E` at which `A` is good has `π(As) ∈ E`, and `A` is a
  bijection, so `μ_S(x_0^-1E) ≤ μ_S(E) + δ`.
  - Running the same count with `A^-1` gives the reverse inequality, and `x_1` works the same way.
  - So `|μ_S(g^-1E) - μ_S(E)| ≤ δ` for `g ∈ {x_0, x_1}`.
- Let `m` be a weak*-cluster point of `μ_(S_n)` in the dual unit ball of `ℓ∞(Ω)` (Banach–Alaoglu).
  - `m` is a mean, invariant under `x_0` and `x_1`, hence `F`-invariant.
  - By step 0, `m(Moved(c)) ≥ lim sup (ε - 4δ_n) = ε`.

**2. Models from means.** Let `E = Moved(c)` and `m(E) = η > 0`.
1. **Density.** Let `P` be the finitely supported probability measures on `Ω`. `m` lies in the
   weak*-closure of `P`. Otherwise Hahn–Banach, in the weak* topology, gives a real `f ∈ ℓ∞(Ω)` with
   `m(f) > sup_(μ∈P) μ(f) = sup f`, and no mean satisfies that.
2. **Constraint.** `P_1 = {μ ∈ P : μ(E) > 3η/4}` is convex. `m` lies in its weak*-closure, because
   `{ν : ν(1_E) > 3η/4}` is a weak*-open neighbourhood of `m`.
3. **Day.** Take a net in `P_1` converging weak* to `m`.
   - Along it, `x_iμ - μ → x_i m - m = 0` in `σ(ℓ1, ℓ∞)`, the weak topology of `ℓ1(Ω)`.
   - The set `{(x_0μ - μ, x_1μ - μ) : μ ∈ P_1}` is convex in `ℓ1 ⊕ ℓ1`, so its weak and norm closures
     agree (Mazur).
   - So for every `η' > 0` some `μ ∈ P_1` has `||x_iμ - μ|| < η'` for `i = 0, 1`.
4. **Namioka.** Put `S_r = {ω : μ(ω) > r}` for `r > 0`.
   - `∫_0^∞ |S_r| dr = 1` and `∫_0^∞ |S_r ∩ E| dr = μ(E)`.
   - `∫_0^∞ |x_iS_r Δ S_r| dr = ||x_iμ - μ||`. Here `(x_iμ)(ω) > r` iff `ω ∈ x_iS_r`, and
     `|a - b| = ∫_0^∞ |1_(a>r) - 1_(b>r)| dr` for `a, b ≥ 0`.
   - Let `f(r) = |S_r ∩ E| - (η/2)|S_r|` and `h(r) = Σ_i |x_iS_r Δ S_r|`. Then `∫f > η/4` and
     `∫h < 2η'`.
   - With `λ = η/(16η')`, `∫(f - λh) > η/8`, so some `r` has `f(r) > λh(r) ≥ 0`.
   - `S = S_r` is then finite and nonempty, with `|S ∩ E| > (η/2)|S|` and
     `h(r) < f(r)/λ ≤ (16η'/η)|S|`.
5. **Model.**
   - Let `A = x_0` on `S ∩ x_0^-1S`. Let `A` map `S \ x_0^-1S` bijectively onto `S \ x_0S`, which
     has the same size. Build `B` from `x_1` the same way.
   - The error is at most `max_i |x_iS \ S|/|S| = max_i |x_iS Δ S|/(2|S|) < 8η'/η`.
   - Choose `η' = ηδ/8`. By step 0, both relator defects are at most `14δ`, and
     `d(AB,BA) ≥ |S ∩ E|/|S| - 4δ > η/2 - 4δ`.
6. **Soficity.** Take `δ ≤ η/32`.
   - These are almost-solutions of both relators with defect at most `14δ`, which goes to 0 as
     `δ → 0`, and `d(AB,BA) > η/4`.
   - That is the negation of form 3 of `thompson-f-sofic-iff-relator-system-unstable`, so `F` is
     sofic.

**3. Uniform mass.** Let `φ(g) = m(1_(Fix(g)))`.
- `φ(e) = 1`, and `φ` is a class function because `Fix(hgh^-1) = h Fix(g)` and `m` is invariant.
- **Positive definite.** Take `g_1, ..., g_r ∈ F` and `z ∈ C^r`.
  - `g_j^-1 g_i ω = ω` iff `g_i ω = g_j ω`.
  - So pointwise `Σ_(i,j) z_i conj(z_j) 1[g_j^-1 g_i ω = ω] = Σ_(x ∈ Ω) |Σ_(i : g_iω = x) z_i|² ≥ 0`.
  - `m` is positive.
- So `φ` is a character of `F`. By `thompson-f-character-simplex` it takes a single value on
  `F' \ {e}`, and `m(Moved(g)) = 1 - φ(g)`.

**4. Slabs.** Let `κ(y) = m(p^-1[0,y))` for `y ∈ (0,1)`.
- `κ` is nondecreasing.
- Every `f ∈ F` is increasing and fixes 0, so equivariance gives `p^-1[0, f(y)) = f·p^-1[0,y)`, and
  `κ(f(y)) = κ(y)`.
- `x_0(u) < u` on `(0,1)`, and 0 and 1 are its only fixed points, so `x_0^n(z) → 0` for every `z < 1`.
  For `0 < y < z < 1` pick `n` with `x_0^n(z) < y`. Then `κ(z) = κ(x_0^n z) ≤ κ(y) ≤ κ(z)`.
- So `κ` is constant on `(0,1)`, and `m(p^-1[y,z]) ≤ κ(z') - κ(y) = 0` for any `z' ∈ (z,1)`.

**5. Corollaries.**
- **Kernel.** Suppose `n ≠ e` acts trivially on `Ω`, and `n(u) ≠ u` for some `u ∈ (0,1)`.
  - Take a dyadic interval `J ∋ u` with `n(J) ∩ J = ∅`, and `g ∈ F' \ {e}` supported in `J`.
  - Then `[n, g] = (n g n^-1) g^-1` lies in `F'`. It is nontrivial, since its factors are nontrivial
    with disjoint supports.
  - It acts trivially, because `n` does. By step 3, `t = m(Moved([n,g])) = 0`.
- **Confined moved sets.** `m(Moved(g)) ≤ Σ_i m(p_i^-1[y,z]) = 0` by step 4, so `t = 0` by step 3.
- **Instances.** Let `g ∈ F' \ {e}` be supported in `[y,z] ⊂ (0,1)`.
  - Points of `(0,1)`: `p = id`.
  - `k`-point configurations: `p_i` is the `i`-th point.
  - Closed intervals: `p_i` are the endpoints.
  - Germs at points: `p` is the base point, since `g` is the identity near every point outside
    `[y,z]`.
  - The Cantor set with the prefix action: `p` is the binary value. A point whose value lies outside
    `[y,z]` lies in a cylinder over `[0,y)` or `(z,1]`, where `g` acts as the identity.
