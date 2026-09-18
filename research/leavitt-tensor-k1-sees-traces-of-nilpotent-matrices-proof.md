---
rg: 2
id: leavitt-tensor-k1-sees-traces-of-nilpotent-matrices-proof
kind: route
title: Tail-orbit traces on L_k(1,2) and the logarithmic derivative of the grading give a K_1 detector for nilpotent coefficient traces
target: leavitt-tensor-k1-sees-traces-of-nilpotent-matrices
requires: []
---

Notation as in the target. `L` is `Z`-graded by `deg e_i = 1`, `deg e_i^* = -1`.
The relations `e_i^* e_j = δ_ij` and `e_1 e_1^* + e_2 e_2^* = 1` are homogeneous,
so the grading is well defined. `L` is spanned by monomials `e_α e_β^*`, where
`α, β` are words in `{1,2}` and `deg e_α e_β^* = |α| - |β|`. So `L_d` is
spanned by the monomials of degree `d`, and `[L,L]` is spanned by the
homogeneous commutators `[u,v]` of monomials.

**Step 1 (a tail-orbit representation).** Let `Ω` be the set of infinite words
over `{1,2}` that are eventually `1^∞`, and `V = k^(Ω)` with basis `δ_y`.
Put `π(e_i)δ_y = δ_(iy)`, and `π(e_i^*)δ_(jy) = δ_ij δ_y`.
- Every `y ∈ Ω` is uniquely `jy'` with `y' ∈ Ω`, so `π(e_i^*)` is well defined.
- `π(e_i^*)π(e_j)δ_y = δ_ij δ_y`.
- `Σ_i π(e_i)π(e_i^*)δ_(jy) = δ_(jy)`.

So `π` is a representation of `L`. For a monomial `u = e_α e_β^*`, `π(u)` is
the partial bijection `βz ↦ αz` of `Ω`, extended by `0`. Every product of such
operators is again a partial bijection extended by `0`.

**Step 2 (diagonal entries of nonzero degree are finite).** Let `u = e_α e_β^*`
with `|α| - |β| = d >= 1`. A diagonal entry at `y` needs `y = βz = αz`. Then `α`
has `β` as a prefix, `α = βγ` with `|γ| = d`, and `γz = z`. So `z = γ^∞`, which
lies in `Ω` only if `γ = 1^d`. Hence `π(u)` has at most one nonzero diagonal
entry. It is `1`, at `y = β1^∞`, when `α = β1^d`, and there is none otherwise.
By linearity, for `c ∈ L_d` with `d >= 1`, `π(c)` has finitely many nonzero
diagonal entries. Define

`τ_m(c) = Σ_(y ∈ Ω) π(c_m)_(yy)`, where `c_m` is the degree-`m` component,

a linear map `L -> k` for each `m >= 1`. Also `τ_m(e_1^j) = δ_jm` for `j >= 1`:
the only fixed point of `1^j z = z` is `z = 1^∞`.

**Step 3 (τ_m vanishes on [L,L]).** It suffices to take monomials `u, v`.
- If `deg u + deg v != m`, then `[u,v]` is homogeneous of another degree, and
  `τ_m([u,v]) = 0`.
- Otherwise `uv` and `vu` lie in `L_m`. `π(u)` and `π(v)` are partial bijections
  `p, q` of `Ω`, so the diagonal entries of `π(uv)` are `0` or `1`. Hence
  `τ_m(uv) = #Fix(p∘q)`, which is finite by Step 2. Likewise
  `τ_m(vu) = #Fix(q∘p)`.
- `y ↦ q(y)` maps `Fix(p∘q)` bijectively onto `Fix(q∘p)`: if `p(q(y)) = y`, then
  `q(p(q(y))) = q(y)`, and the inverse is `z ↦ p(z)`.

So `τ_m(uv) = τ_m(vu)`.

**Step 4 (a trace on R).** For `φ` as in the target, put
`T(b ⊗ c) = φ(b) τ_m(c)`, a linear map `R -> k`. For simple tensors,

`[a ⊗ c, a' ⊗ c'] = [a,a'] ⊗ cc' + a'a ⊗ [c,c']`.

Its image under `T` is `φ([a,a']) τ_m(cc') + φ(a'a) τ_m([c,c']) = 0`, by the
hypothesis on `φ` and Step 3. So `T([R,R]) = 0`.

**Step 5 (logarithmic derivative).** Let `D` be a derivation of a ring `R` and
`T : R -> A` additive with `T([R,R]) = 0`. Extend `D` entrywise to a derivation
of `M_n(R)`. Define `Θ(u) = T(tr(u^(-1) D(u)))` on `GL_n(R)`.
- *Cyclicity.* `tr(PQ) - tr(QP) = Σ_(ij) [P_ij, Q_ji] ∈ [R,R]`, so
  `T(tr(v^(-1) X v)) = T(tr X)`.
- *Multiplicativity.* By Leibniz,
  `(uv)^(-1) D(uv) = v^(-1) (u^(-1) D(u)) v + v^(-1) D(v)`. So
  `Θ(uv) = Θ(u) + Θ(v)`.
- *Stability.* `Θ(diag(u, 1)) = Θ(u)`.

So `Θ` is a homomorphism `GL(R) -> A` into an abelian group. It kills
`[GL(R), GL(R)] = E(R)`, so it factors through `K_1(R)`.

**Step 6 (evaluation).** Take `R = B ⊗ L`, `D = id ⊗ ∂` with `∂(c) = d·c` for
`c ∈ L_d`, and `T` from Step 4. `∂` is a derivation because
`deg(cc') = deg c + deg c'`, so `D` is a derivation of `R`. Let `χ_(φ,m)` be the
induced map on `K_1(R)`.

For nilpotent `x ∈ M_n(B)`, use `M_n(R) = M_n(B) ⊗ L`. Then `u = 1 + x ⊗ e_1`
is invertible with `u^(-1) = Σ_(j>=0) (-1)^j x^j ⊗ e_1^j`, a finite sum. Also
`D(u) = x ⊗ e_1`, so

`tr(u^(-1) D(u)) = Σ_(j>=1) (-1)^(j-1) tr(x^j) ⊗ e_1^j`.

By Step 2, `τ_m(e_1^j) = δ_jm`. So `χ_(φ,m)[u] = (-1)^(m-1) φ(tr x^m)`. This
proves the Theorem.

**Step 7 (corollaries).**
1. *Screen.* If `tr(x^m) ∉ [B,B]`, a linear `φ` vanishing on the subspace
   `[B,B]` with `φ(tr x^m) = 1` exists, since `k` is a field. Then
   `χ_(φ,m)[1 + x ⊗ e_1] = ±1 != 0`, so `K_1(R) != 0`.
2. *Torsion units.* If `p·1 = 0` and `u^(p^j) = 1`, then
   `(u - 1)^(p^j) = u^(p^j) - 1 = 0`. Apply 1 to the `1 x 1` matrix `x = u - 1`.
3. *Counterexamples.*
   - `B = k[ε]` is commutative, so `[B,B] = 0`, and `tr ε = ε != 0`.
   - `B = k[G]` with `char k = p` and `g ∈ G` of order `p`. Take `φ` to be the
     coefficient sum over the conjugacy class of `g`. It vanishes on `[B,B]`
     because `hh'` and `h'h` are conjugate. `φ(g - 1) = 1` because `g != 1`, and
     `x = g - 1` is nilpotent by 2.
4. *Semisimple Artinian `B = M_r(D)`.* Let `x ∈ M_n(B) = M_(nr)(D)` be nilpotent.
   The kernels `ker x ⊆ ker x^2 ⊆ ...` are `D`-subspaces of `D^(nr)`. A basis
   adapted to this flag gives `x = g s g^(-1)` with `s` strictly upper
   triangular, so `x^m = g s^m g^(-1)`.
   - By Step 5's cyclicity over `D`, `tr_D(x^m) ≡ tr_D(s^m) = 0` modulo `[D,D]`.
   - The map `M_r(D)/[M_r(D), M_r(D)] -> D/[D,D]` induced by the trace is
     injective: a matrix with trace in `[D,D]` differs from a diagonal matrix
     `diag(t, 0, ..., 0)`, with `t ∈ [D,D]`, by off-diagonal matrix units
     `a e_ij = [a e_ii, e_ij]` and differences `a e_ii - a e_11 = [a e_i1, e_1i]`.
     And `t e_11` is a sum of commutators `[a e_11, b e_11]`.

   So `tr(x^m) ∈ [B,B]`. ∎
