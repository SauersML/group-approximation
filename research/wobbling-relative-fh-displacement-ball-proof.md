---
rg: 2
id: wobbling-relative-fh-displacement-ball-proof
kind: route
title: "Cut-space vectors: generators move the scale-n smeared cut by 4r^2/n, a far jump across the cut moves it by sqrt 2, and Lemma Q makes the bound uniform"
target: wobbling-relative-fh-subsets-lie-in-displacement-balls
requires: []
---

Notation is as in `wobbling-relative-fh-subsets-lie-in-displacement-balls`. Here `Γ = ⟨Q⟩` is f.g.,
`ρ: Γ → W(Z)`, `r = max_Q disp(ρ(q))`, and `Y ⊆ Γ` has relative FH. A **cnd function** is a
conditionally negative definite `ψ: Γ → [0,∞)` with `ψ(1) = 0` and `ψ(g^{-1}) = ψ(g)`.

## Step 1 (Lemma Q: uniform comparison with the generators)

**Claim.** There is `C < ∞` with `sup_Y ψ ≤ C · max_Q ψ` for every cnd `ψ` on `Γ`.

- For a cnd `ψ`, `√ψ` is subadditive. Write `ψ = ‖b‖²` for a 1-cocycle `b`; then
  `‖b(gh)‖ ≤ ‖b(g)‖ + ‖b(h)‖`. So `ψ(g) ≤ |g|_Q² · max_Q ψ`.
- Suppose no `C` works. Then for each `j ≥ 1` there is a cnd `ψ_j` with `max_Q ψ_j = 1` and
  `sup_Y ψ_j ≥ 4^j`. If `max_Q ψ = 0`, then `ψ ≡ 0` by the previous bullet, so rescaling to
  `max_Q ψ_j = 1` is allowed.
- Put `Ψ = Σ_j 2^{-j} ψ_j`. The series converges pointwise, because `ψ_j(g) ≤ |g|_Q²`.
  Cnd functions form a convex cone that is closed under pointwise limits, so `Ψ` is cnd.
- But `sup_Y Ψ ≥ 2^{-j} 4^j = 2^j` for every `j`, so `Ψ` is unbounded on `Y`. This contradicts
  relative FH.

## Step 2 (cut-space vectors)

- `C = {A ⊆ Z : A Δ N finite}` is countable. `W(Z)` acts on it by `A ↦ gA`. Indeed `gN Δ N` is
  finite: if `x ≥ 0 > gx` then `x < disp(g)`, and if `y ≥ 0 > g^{-1}y` then `y < disp(g)`.
  So `Γ` acts on `ℓ²(C)` by `(π(g)f)(A) = f(ρ(g)^{-1}A)`, and `ψ_ξ(g) = ‖π(g)ξ − ξ‖²` is cnd for
  every `ξ ∈ ℓ²(C)`.
- Fix a cut `m ∈ Z` and a scale `n ≥ 1`. Put `θ(u) = clip(2 − |u|/n, 0, 1)`. So `θ = 1` on
  `|u| ≤ n`, `θ = 0` on `|u| ≥ 2n`, and `θ` is `1/n`-Lipschitz. Put `p(y) = θ(y − m)²/2 ∈ [0, 1/2]`.
- Let `E ⊆ Z` be random with independent coordinates, `P(y ∈ E) = p(y)`. Then
  `E ⊆ [m − 2n, m + 2n]`, so `A = [m, ∞) Δ E ∈ C`. Let `μ = μ_{m,n}` be the law of `A`, and put
  `ξ = √μ`. This is a unit vector.
- **Image law.** For `g ∈ W(Z)`, `gA = g[m,∞) Δ gE = [m,∞) Δ D Δ gE`, with
  `D = g[m,∞) Δ [m,∞)`, a finite deterministic set. `gE` has independent coordinates with
  `P(y ∈ gE) = p(g^{-1}y)`. So `g_*μ` is the law of `[m,∞) Δ E'`, where `E'` has independent
  coordinates with `P(y ∈ E') = p'(y)`, and
  - `p'(y) = p(g^{-1}y)` if `y ∉ D`;
  - `p'(y) = 1 − p(g^{-1}y)` if `y ∈ D`.
- Since `A ↦ A Δ [m,∞)` is a bijection, `⟨π(g)ξ, ξ⟩ = Σ_A √(μ(A) g_*μ(A)) = ∏_y BC(p(y), p'(y))`,
  where `BC(a,b) = √(ab) + √((1−a)(1−b))`. The product has only finitely many factors `≠ 1`. So

  `‖π(g)ξ − ξ‖² = 2 (1 − ∏_y BC(p(y), p'(y)))`.  (★)

## Step 3 (Lemma A: generators move ξ by at most 4r²/n)

**Claim.** If `disp(g) ≤ r` and `n ≥ 2r`, then `‖π(g)ξ − ξ‖² ≤ 4r²/n`, for every cut `m`.

- **On `D`.** If `y ∈ D`, then `y` and `g^{-1}y` lie on opposite sides of `m`, and
  `|g^{-1}y − y| ≤ r`. So `y ∈ [m − r, m + r − 1]` and `|g^{-1}y − m| ≤ 2r ≤ n`. Both points lie
  in the flat zone, so `p(y) = p(g^{-1}y) = 1/2` and `p'(y) = 1/2`. Hence `BC = 1` on `D`.
- **Off `D`.** Here `p'(y) = p(g^{-1}y)`. Write `θ_1 = θ(y − m)`, `θ_2 = θ(g^{-1}y − m)`,
  `a = θ_1²/2` and `b = θ_2²/2`. Then
  `1 − BC(a,b) = ½[(√a − √b)² + (√(1−a) − √(1−b))²]`.
  - `√a − √b = (θ_1 − θ_2)/√2`.
  - On `[0, ½]`, `|d/dx √(1−x)| ≤ 1/√2`. So `|√(1−a) − √(1−b)| ≤ |a − b|/√2 ≤ |θ_1 − θ_2|/√2`,
    using `|θ_1² − θ_2²| ≤ 2|θ_1 − θ_2|`.
  - Hence `1 − BC ≤ (θ_1 − θ_2)²/2 ≤ (r/n)²/2`, since `θ` is `1/n`-Lipschitz.
- **Support.** `θ_1 ≠ θ_2` forces `n − r < |y − m| < 2n + r`. If `|y − m| ≤ n − r`, both
  arguments lie in `|u| ≤ n`. If `|y − m| ≥ 2n + r`, both lie in `|u| ≥ 2n`. That leaves at most
  `2(n + 2r − 1)` integers `y`.
- **Sum.** All factors lie in `[0,1]`, so `1 − ∏ BC_y ≤ Σ_y (1 − BC_y)`. By (★),
  `‖π(g)ξ − ξ‖² ≤ 2 · 2(n + 2r − 1) · r²/(2n²) ≤ 4r²/n`, using `n + 2r − 1 ≤ 2n`.

The artifact `check_cut_space_vectors.py` checks this exactly by computing (★) over 959 random
wobbles. The largest ratio to the bound was `0.31`.

## Step 4 (Lemma B: a far jump across the cut is singular)

**Claim.** Suppose `h ∈ W(Z)` and `z ∈ Z` satisfy `|z − m| ≥ 2n` and `|hz − m| ≥ 2n`, with `z` and
`hz` on opposite sides of `m`. Then `μ ⟂ h_*μ`, and `‖π(h)ξ − ξ‖² = 2`.

- Say `z < m ≤ hz`. The other case is symmetric.
- Under `μ`: `p(hz) = 0`, so `hz ∉ E` almost surely. Since `hz ≥ m`, this gives `hz ∈ A` almost
  surely.
- Under `h_*μ`, the law of `hA`: `hz ∈ hA` iff `z ∈ A`. But `z < m` and `p(z) = 0`, so `z ∉ A`
  almost surely. So `hz ∉ hA` almost surely.
- So the event `{hz ∈ A}` has `μ`-measure 1 and `h_*μ`-measure 0. Then `⟨π(h)ξ, ξ⟩ = 0`, and
  `‖π(h)ξ − ξ‖² = 2`.

The artifact checks 9 such cases, and every one gives exactly `2`.

## Step 5 (Theorem W)

- Take `C` from Step 1, and an integer `n > max(2Cr², 2r)`.
- For every cut `m`, `ψ_{m,n} = ‖π(·)ξ_{m,n} − ξ_{m,n}‖²` is cnd on `Γ`. By Step 3,
  `max_Q ψ_{m,n} ≤ 4r²/n`, so `sup_Y ψ_{m,n} ≤ 4Cr²/n < 2`.
- Suppose `y ∈ Y` and `h = ρ(y)` has `hz − z ≥ 4n` for some `z`. Put `m = z + 2n`. Then
  `z = m − 2n` and `hz ≥ m + 2n`, so Step 4 gives `ψ_{m,n}(y) = 2`. That is a contradiction.
- If instead `hz − z ≤ −4n`, put `m = z − 2n`. Then `z − m = 2n` and `hz ≤ m − 2n`. The same
  contradiction follows.
- So `disp(ρ(y)) < 4n` for every `y ∈ Y`. The constant `C` depends only on `(Γ, Q, Y)`, and not on
  `ρ`.

## Step 6 (corollaries)

**(a) Subgroups of `W(Z)`.** Let `(Γ, H)` have relative (T). Then `Y = H` has relative FH
(BdlHV Thm 2.12.4), so every element of `ρ(H)` has displacement `≤ K = 4n − 1`. Since `ρ(H)` is a
group, each `ρ(H)`-orbit lies in `[z − K, z + K]` and has at most `2K + 1` points. So `ρ(H)`
embeds in `∏_O Sym(O)`, a product of groups of order `≤ N = (2K+1)!`.

Let `H' ≤ ρ(H)` be generated by `d` elements. The image of a word in the factor `Sym(O)` is
determined by the `d`-tuple of generator images, after identifying `O` with a subset of
`{1, …, 2K+1}`. There are only finitely many such tuples. So `H'` embeds in a finite product of
finite groups, and `H'` is finite. The exponent divides `N`.

**(b) The full shift.** Let `Γ ≤ [[X]]` be generated by a finite symmetric `Q`, and put
`r = max_Q ‖k_q‖_∞`. Let `Y ⊆ Γ` have relative FH.

- For each `x` with aperiodic `σ`-orbit, `j ↦ σ^j x` identifies the orbit with `Z`. Then
  `f ∈ Γ` acts on it by `j ↦ j + k_f(σ^j x)`. This is a homomorphism `ρ_x: Γ → W(Z)` with
  generator displacement `≤ r`.
- Step 1's `C` does not depend on `ρ`. So Step 5, with one `n`, gives `|k_y(σ^j x)| < 4n` for all
  `y ∈ Y`, all aperiodic `x` and all `j`.
- Aperiodic points are dense in `X`, and `k_y` is continuous and integer-valued. So
  `‖k_y‖_∞ ≤ K = 4n − 1`, that is, `Y ⊆ B_K`.

**(c) Relative-(T) subgroups of `[[X]]`: local finiteness and bounded exponent.** Let
`H ≤ Γ ≤ [[X]]` with `(Γ, H)` relative (T). By (b), `H ⊆ B_K`. This is the Step 1 argument of
`full-shift-topological-full-groups-are-torsion-locally-finite`, which uses no torsion hypothesis.

- **Exponent.** On each aperiodic orbit, every `h ∈ H` has cycles of length `≤ 2K + 1`. So
  `h^{(2K+1)!}` is the identity on a dense set, hence everywhere.
- **Local finiteness.** Let `H' = ⟨h_1, …, h_d⟩ ≤ H`, and let `L` be such that every `k_{h_i}`
  depends only on `x_{[−L, L]}`.
  - For aperiodic `x` and `j ∈ Z`, the `H'`-orbit of `j` lies in `[j − K, j + K]`. The action of
    each `h_i` on those points reads only `x_{[j−K−L, j+K+L]}`.
  - So the finite `H'`-set `H'·j`, with a base point, is determined by a word `w` of length
    `2(K+L)+1`. This gives a homomorphism `H' → Sym(2K+1)` for each such `w`.
  - An element acting trivially on all of these finite sets acts trivially on every aperiodic
    orbit, hence is trivial.
  - So `H'` embeds in a product of at most `2^{2(K+L)+1}` finite groups, and `H'` is finite.

## Where it stops

This proves nothing positive about the Haagerup property. A relative-(T) refutation can still live
inside one ball `B_K` with bounded exponent. See the claim's "What survives": the char-p candidate,
and the monomial block representation test.
