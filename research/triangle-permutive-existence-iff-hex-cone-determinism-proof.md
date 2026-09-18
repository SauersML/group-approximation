---
rg: 2
id: triangle-permutive-existence-iff-hex-cone-determinism-proof
kind: route
title: A rational linear change of lattice and a triangular higher-block code turn three-cone determinism into triangle permutivity, and cone filling gives the determining normals
target: triangle-permutive-existence-iff-hex-cone-determinism
requires: []
---

Notation is as in the target. `<.,.>` is the standard inner product. For finite `K ⊆ Z^2`, `R_K = max_(k ∈ K) |k|`.
Recalled results:
- Curtis–Hedlund–Lyndon: conjugacies of `Z^d`-subshifts are sliding block codes.
- Evans (1960): a partial Latin square of order `m` embeds in a Latin square of order `2m`.
- For a minimal action of an abelian group `G` and a finite-index subgroup `H`, the space is a finite disjoint
  union of clopen `H`-minimal sets.

The last item has a short proof. Take an `H`-minimal closed set `M`, which exists by Zorn. Each `gM` is
`H`-minimal, because `H` is normal. The finite union `∪ gM` over coset representatives is closed and
`G`-invariant, so it is everything. Two `H`-minimal sets are equal or disjoint. Hence the distinct `gM` form a
finite closed partition, so they are clopen.

## 1. Cone lemma

**Lemma 1.** Let `m ∈ R^2 \ {0}`.
- `<s,m> < 0` for all `s ∈ S_1` iff `m_2 > 0` and `m_2 > m_1`.
- `<s,m> < 0` for all `s ∈ S_2` iff `m_1 > 0` and `m_1 > m_2`.
- `<s,m> < 0` for all `s ∈ S_3` iff `m_1 < 0` and `m_2 < 0`.

If `m` is not a positive multiple of `(1,1)`, `(0,-1)` or `(-1,0)`, then at least one of the three holds.

*Proof.* `S_1 \ {0}`, `S_2 \ {0}` and `S_3` are the closed cones spanned by `{(0,-1),(1,-1)}`, `{(-1,0),(-1,1)}`
and `{(1,0),(0,1)}`, minus the origin. A linear functional is negative on such a cone iff it is negative on both
generators. That gives `-m_2 < 0, m_1 - m_2 < 0`, then `-m_1 < 0, -m_1 + m_2 < 0`, then `m_1 < 0, m_2 < 0`.

Suppose all three fail.
- If `m_1, m_2 <= 0`, the third fails only if one coordinate is `0`. The other is then negative, since `m ≠ 0`.
  So `m = (0,-t)` or `(-t,0)` with `t > 0`.
- Otherwise some coordinate is positive. Say `m_2 > 0`. The first fails, so `m_1 >= m_2 > 0`. The second fails, so
  `m_2 >= m_1`. Hence `m_1 = m_2 > 0`.
- The case `m_1 > 0` is symmetric. ∎

## 2. Rational witnesses

**Lemma 2.** If `(K_1,K_2,K_3)` is hex-alternate, then every witness `A` is invertible. Some witness is rational,
and it can be chosen with `A^(-1)` an integer matrix.

*Proof.* **Invertible.** `A ≠ 0`, since `0 ∉ S_j`. Suppose `A` has rank 1, with image the line `Rd`. Then `Rd`
meets `S_3`, so we may take `d_1, d_2 >= 0`. It also meets `S_1`. Since `d ∉ S_1` (that needs `d_2 < 0`), we get
`-d ∈ S_1`, so `0 <= -d_1 <= d_2`, hence `d_1 = 0`. Then `Rd` is the vertical axis, which misses `S_2`, because
`S_2` needs `p < 0`. That contradicts `A(K_2) ⊆ S_2 ≠ ∅`.

**Rational.** The witness set `W = {A ∈ R^(2×2) : A k ∈ S_j for all j, k ∈ K_j}` is defined by finitely many
linear inequalities in the entries of `A`, some strict, all with integer coefficients. Take `A_0 ∈ W`. Let `V` be
the linear subspace cut out by the non-strict inequalities that are equalities at `A_0`. It is defined over `Q`,
so `V ∩ Q^4` is dense in `V`. Every other inequality holds strictly at `A_0`, and so on a neighbourhood of `A_0`
in `V`. That neighbourhood meets `Q^4`.

**Integer inverse.** Every `S_j` is invariant under positive scaling. If `A` is a rational witness and `m` clears
the denominators of `A^(-1)`, then `A' = m^(-1)A` is a witness with `A'^(-1) = mA^(-1)` integral. ∎

## 3. Theorem A, (2) ⇒ (1)

Let `Ω_0` be a free minimal SFT, `(K_1,K_2,K_3)`-deterministic with functions `f_j`. Every `K_j` is nonempty by
definition. By Lemma 2, fix a rational witness `A` with `A^(-1)` integral. Put `Λ = A^(-1)Z^2`, a finite-index
subgroup of `Z^2`, and `L = A Z^2`, a lattice containing `Z^2`. Transport points: `x̃(Aw) = x(w)` for `w ∈ Z^2`,
so `x̃ ∈ Σ^L`. Determinism becomes `x̃(v) = f_j(x̃|(v + A K_j))` with `A K_j ⊆ S_j`. Let
`R = max_j max_(k ∈ K_j) |A k|_∞`, and fix an integer `N >= 2R + 2`.

Let `Δ_N = {(a,c) ∈ R^2 : a, c >= 0, a + c <= N}`, `D_N = L ∩ Δ_N` and `B = A^(-1) D_N ⊆ Z^2`. Define
`Φ(x)(u) = x̃|(u + D_N)` for `u ∈ Z^2`, a pattern on the fixed finite set `D_N`. Let `Q_0` be the finite set of
patterns occurring, and `Y = Φ(Ω_0) ⊆ Q_0^(Z^2)`.

**3.1. Y is a Z^2-SFT conjugate to (Ω_0, Λ).**
- `Φ(σ^λ x) = σ^(Aλ) Φ(x)` for `λ ∈ Λ`.
- `Φ` is continuous. It is injective: `Δ_N ⊇ [0,1)^2` because `N >= 2`, and `L ∩ [0,1)^2` is a fundamental domain
  for `Z^2` in `L`. So the blocks `u + D_N` cover `L`.
- `Y` consists of the `y ∈ Q_0^(Z^2)` such that (a) `y(u)` and `y(u')` agree on `(u + D_N) ∩ (u' + D_N)` whenever
  this is nonempty, which forces `u - u'` into a finite set, and (b) the configuration `x̃` assembled from `y` by
  (a) avoids the finitely many forbidden patterns of `Ω_0`, transported to `L`.
- Condition (b) is local. A forbidden pattern on `F`, placed at `v ∈ L`, is covered by the blocks `u + D_N` with
  `u` in `v - [0,1)^2` plus a fixed finite set. Only finitely many classes `v mod Z^2` exist.
- So `Y` is defined by finitely many forbidden patterns, and `Φ` conjugates `(Ω_0, Λ)`, with `Λ` read through `A`
  as `Z^2`, onto `(Y, Z^2)`.

**3.2. Triangle permutivity of Y.** In coordinates `(a,c)` of `R^2`, `Δ_N ∪ (Δ_N + e_1) ∪ (Δ_N + e_2) = Δ_(N+1)`
for `N >= 1`. A point of `Δ_(N+1) \ Δ_N` has `a >= 1` or `c >= 1`, since `a, c < 1` would force `a + c < 2 <= N`.

(i) *`y(u+e_2)` from `y(u)` and `y(u+e_1)`.* We know `x̃` on `u + (Δ_N ∪ (Δ_N+e_1)) ∩ L` and need it on
`u + (Δ_N + e_2)`. The missing points `v = u + (a,c)` lie in the strip `P_1 = {0 <= a < 1, c >= 1, N < a + c <= N+1}`.
On `P_1` we have `c > N - 1 >= R`. Order `P_1 ∩ (L - u)` by increasing `c`, a finite set, and apply `f_1`. For
`s = (p,q) ∈ A K_1 ⊆ S_1` we get `v + s = u + (a+p, c+q)` with:
- `a + p >= 0`, because `p >= 0`;
- `c + q >= c - R > 0`;
- `(a+p) + (c+q) <= a + c <= N + 1`, because `p + q <= 0`;
- `c + q < c`.

So `v + s ∈ u + Δ_(N+1)`. Either it is known (in `Δ_N` or `Δ_N + e_1`), or it lies in `P_1` with smaller
`c`-coordinate and was filled earlier.

(ii) *`y(u+e_1)` from `y(u)` and `y(u+e_2)`.* Symmetrically, the missing points lie in
`P_2 = {0 <= c < 1, a >= 1, N < a + c <= N+1}`. Fill by increasing `a` with `f_2`. For `(p,q) ∈ S_2`: `q >= 0`,
`a + p >= a - R > 0`, `p + q <= 0` and `p < 0`.

(iii) *`y(u)` from `y(u+e_1)` and `y(u+e_2)`.* The missing points are `P_3 = {0 <= a < 1, 0 <= c < 1}`. Fill by
decreasing `a + c` with `f_3`. For `(p,q) ∈ S_3`:
- `a + p, c + q >= 0`;
- `(a+p) + (c+q) < 2 + 2R <= N`, so the point lies in `Δ_(N+1)`;
- `(a+p) + (c+q) > a + c`, because `p, q >= 0` and `s ≠ 0`.

So `v + s` is known or lies in `P_3` with larger `a + c`.

In each case the procedure uses only `f_j` and the two given blocks. So on the set `T ⊆ Q_0^3` of triples
`(y(u), y(u+e_1), y(u+e_2))` occurring in `Y`, each coordinate is a function of the other two.

**3.3. Quasigroup.** Such a `T` is a partial Latin square of order `m = |Q_0|`: row `a`, column `b`, entry `c`, and
no symbol repeats in a row or a column. By Evans it embeds in a Latin square, the table of a quasigroup `(Q', ⋆)`
of order `2m` with `Q_0 ⊆ Q'` and `a ⋆ b = c` for all `(a,b,c) ∈ T`. Hence `Y ⊆ X_⋆`. As a subset of
`Q'^(Z^2)`, `Y` is still an SFT: forbid the letters of `Q' \ Q_0`.

**3.4. Free minimal piece.** `(Ω_0, Z^2)` is minimal, so `Ω_0` is a finite disjoint union of clopen `Λ`-minimal
sets `M_i`. Each `Φ(M_i)` is clopen in `Y`, shift-invariant and minimal.

A clopen invariant subset `C` of an SFT is an SFT. `C` is a finite union of cylinders on some window `W`. Then
`C = {y ∈ Y : y|(u+W)` is a `C`-pattern for every `u}`, by invariance, and that is finitely many extra forbidden
patterns.

`Φ(M_i)` is free, because `Λ` acts freely on `Ω_0`. So `Φ(M_1) ⊆ X_⋆` is a free minimal sub-SFT, which is (1). ∎

## 4. Theorem A, the remaining implications

**(1) ⇒ (3).** Take `r = 1` and `f(a,b) = a ⋆ b`. This is bipermutive, because `(Q, ⋆)` is a quasigroup.

**(3) ⇒ (2).** Let `Ω` be a free minimal sub-SFT of the radius-`r` bipermutive spacetime of `f`. Every point of the
spacetime, and so every point of `Ω`, satisfies three determinism rules.
- The top cell `w = z + e_2` is `f` of `w + K_1`, with `K_1 = {(k,-1) : 0 <= k <= r}`.
- The rightmost cell `w = z + r e_1` is determined by `w + K_2`, with `K_2 = {(-k,0) : 1 <= k <= r} ∪ {(-r,1)}`. Here
  `f` is permutive in its last variable, and `(-r,1)` is the position `z + e_2`.
- The leftmost cell `w = z` is determined by `w + K_3`, with `K_3 = {(k,0) : 1 <= k <= r} ∪ {(0,1)}`. Here `f` is
  permutive in its first variable.

With `A = diag(1, r)`:
- `A(k,-1) = (k,-r) ∈ S_1`, since `0 <= k <= r`;
- `A(-k,0) = (-k,0) ∈ S_2`, and `A(-r,1) = (-r,r) ∈ S_2`;
- `A(k,0) = (k,0) ∈ S_3`, and `A(0,1) = (0,r) ∈ S_3`.

So the triple is hex-alternate, and `Ω` witnesses (2). ∎

## 5. Theorem B

**B.1 (conjugacy invariance).** Let `φ : Ω -> Ω'` be a conjugacy. By Curtis–Hedlund–Lyndon, `φ` and `φ^(-1)` are
block codes of some radius `ρ` (sup norm). Suppose `n` is determining for `Ω`, and `x', y' ∈ Ω'` agree on
`H_t = {<z,n> < t}`. Then `φ^(-1)x'` and `φ^(-1)y'` agree on `H_(t - ρ|n|_1)`, so they are equal, and so are
`x'` and `y'`. The converse is symmetric. ∎

**B.4, and hence B.2.** Let `Ω` be `(K_1,K_2,K_3)`-deterministic with witness `A`, and let `n` lie off
`A^T R_(>0)(1,1)`, `A^T R_(>0)(0,-1)` and `A^T R_(>0)(-1,0)`. Put `m = A^(-T) n`. Then `m` is off the three rays,
and by Lemma 1 there is a `j` with `<s,m> < 0` on `S_j`. For `k ∈ K_j`, `<k,n> = <Ak, m> < 0`. Let
`ε = min_(k ∈ K_j) (-<k,n>) > 0`.

Suppose `x, y ∈ Ω` agree on `H_t`. By induction on `i >= 0`, they agree on `H_(t + iε)`. If `z` satisfies
`t + iε <= <z,n> < t + (i+1)ε`, every `z + k` with `k ∈ K_j` has `<z+k,n> <= <z,n> - ε < t + iε`. So
`x(z) = f_j(x|(z+K_j)) = f_j(y|(z+K_j)) = y(z)`. Every `z` lies in some `H_(t+iε)`, so `x = y`.

Any closed shift-invariant `Ω ⊆ X_⋆` is deterministic for the triangle triple with `A = I`, since `⋆` is a
quasigroup. That gives B.2. ∎

**Expansiveness (B.2, second sentence).** Let `n` and `-n` both lie off the three rays. Take `j_+` and `j_-` from
Lemma 1 for `n` and `-n`, and let `ε > 0` be the smaller of the two gaps. Let `R' = max |<k,n>|` over
`k ∈ K_(j_+) ∪ K_(j_-)`, and let `U = {z : |<z,n>| <= R'}` be the strip.

Suppose `x, y ∈ Ω` agree on `U`. A point `z` with `R' <= <z,n> < R' + ε` needs, through `f_(j_+)`, only the cells `z + k` with `<z,n> - R' <= <z+k,n> <= <z,n> - ε`, all inside `U`. Inductively, in steps of `ε`, `x` and `y` agree on `{<z,n> >= -R'}`. Running the same induction with `-n` and `f_(j_-)` gives agreement on `{<z,n> <= R'}`. Hence `x = y`. By definition (Boyle–Lind), the line `n^⊥` is
expansive. ∎

**B.3.** A line `n^⊥` is expansive iff a strip `U` of some width determines points. If `n^⊥` is expansive, then
both `±n` are determining, because each half-plane `H_t` contains a strip of any given width. So a
non-determining normal lies on a nonexpansive line. For `Ω ⊆ X_⋆`, the second part of B.2 shows that a
nonexpansive line has `n` or `-n` on one of the three rays. That line is the antidiagonal `(1,1)^⊥`, a row
(`(0,1)^⊥`) or a column (`(1,0)^⊥`). No two of the three rays are antipodal, so at most one of `±n` lies on a
ray, and the other normal is determining by B.2. ∎

## 6. Corollary

Let `Ψ : Ω -> Y ⊆ X_⋆` be a homeomorphism with `Ψ(σ^(Mu) x) = σ^u Ψ(x)` for `u ∈ Z^2`. By the Curtis–Hedlund–Lyndon argument for the `Λ`-action, there is a finite `E ⊆ Z^2` such that `Ψ(x)(u)` depends only on `x|(Mu + E)`. Likewise, there is a finite `E'` such that `x|(Mu + D)`, for a fundamental domain `D` of `Λ` in `Z^2`, depends only on `Ψ(x)|(u + E')`. Now `<Mu, n'> = <u, M^T n'>`. So agreement of `x, x'` on `{<w,n'> < t}` gives agreement of `Ψ(x), Ψ(x')` on `{<u, M^T n'> < t - c}`, for a constant `c`, and conversely. Hence, as in B.1, `n'` is determining for `Ω` iff `M^T n'` is determining for `Y`. The non-determining normals of `Ω` are therefore `M^(-T)` applied to those of `Y`, and by B.2 these lie in the three rays.

`M^(-T)` is rational and invertible. It preserves "no two antipodal" and "0 interior to the convex hull", both
of which hold for `(1,1)`, `(0,-1)`, `(-1,0)`. Hence:
- A two-sided fault (non-determining `n` and `-n`) is excluded, and so are four or more non-determining rays.
- An irrational non-determining normal is excluded, because the rays are rational.
- Three non-determining rays inside an open half-plane are excluded. ∎

## 7. Scope and limits

- Theorem A widens the construction class but does not change the problem. Nothing here produces a free minimal
  example, and nothing rules one out.
- The corollary is necessary, not sufficient.
- It does not address whether Robinson-type or Labbé-type faults are two-sided or irrational in the
  half-plane sense. A nonexpansive direction need not carry a non-determining normal. The existing heuristic
  exclusions in `free-minimal-triangle-permutive-sft-exists` remain heuristic until that is checked for each
  candidate.
