---
rg: 2
id: gap-sofic-approximations-are-local-embeddings-proof
kind: route
title: Proof that gap sofic approximations are local embeddings, with the affine and projective gap bounds
target: gap-sofic-approximations-are-local-embeddings
requires: []
---

**LEF.** `G` is LEF if for each finite `F ⊆ G` there are a finite group `Q` and an injective map
`φ : F -> Q` with `φ(gh) = φ(g) φ(h)` whenever `g, h, gh ∈ F`.

**Facts about `d`.** It is invariant under left and right multiplication in `Sym(Ω)`, satisfies the
triangle inequality, and `d(a, b) = 1 - fpr(b^(-1) a)`.

**(gap ⇒ LEF).** Fix a finite `F` and let `P = {(g, h) ∈ F × F : gh ∈ F}`.
1. For `(g, h) ∈ P` put `x_N = σ_N(gh)^(-1) σ_N(g) σ_N(h) ∈ H_N`. Then
   `fpr(x_N) = 1 - d(σ_N(g) σ_N(h), σ_N(gh)) -> 1`.
2. `P` is finite, so for large `N` every such `x_N` has `fpr(x_N) > 1 - δ`, and the gap gives
   `x_N = 1`. So `σ_N(gh) = σ_N(g) σ_N(h)` for all `(g, h) ∈ P`.
3. For `g ≠ h` in `F`, by invariance and the triangle inequality,
   `d(σ_N(g), σ_N(h)) >= d(σ_N(h) σ_N(h^(-1) g), σ_N(h)) - d(σ_N(h) σ_N(h^(-1) g), σ_N(g))`
   `= d(σ_N(h^(-1) g), 1) - o(1) -> 1`. So `σ_N(g) ≠ σ_N(h)` for large `N`.
4. For large `N`, `σ_N|F : F -> H_N` is an injective partial homomorphism into a finite group.

**(LEF ⇒ gap).** Choose finite sets `F_1 ⊆ F_2 ⊆ ...` exhausting `G`, each containing `e`, and
injective partial homomorphisms `φ_N : F_N -> Q_N`. Then `φ_N(e) = φ_N(e)^2`, so `φ_N(e) = 1`.
- Let `Ω_N = Q_N` and `H_N = Q_N` acting by left multiplication. A nontrivial element has no fixed
  point, so the gap is `1`.
- Put `σ_N(g) = φ_N(g)` for `g ∈ F_N` and `σ_N(g) = 1` otherwise.
- For fixed `g, h`, eventually `g, h, gh ∈ F_N`, and then the relation holds exactly. For `g ≠ e`,
  eventually `φ_N(g) ≠ 1`, which moves every point, so `d(σ_N(g), 1) = 1`.

**Gap (A): affine maps.** Let `A` be a finite group and `x(y) = a α(y)` with `a ∈ A`,
`α ∈ Aut(A)` and `x ≠ 1`.
- If `y_0` is fixed, then `y_0 z` is fixed iff `a α(y_0) α(z) = y_0 z` iff `α(z) = z`. So `Fix(x)`
  is empty or the coset `y_0 A^α` of the fixed subgroup `A^α`.
- If `A^α = A`, then `α = 1` and `x(y) = a y` with `a ≠ 1`, which has no fixed point. Otherwise
  `A^α` has index at least `2`.
- So `fpr(x) ≤ 1/2`. These maps form the group `A ⋊ Aut(A)`, which contains `GL_m(F_q)` and
  `AGL_m(F_q)` acting on `A = F_q^m`, and `Aut(A)` acting on `A`.

**Gap (P): projective linear maps.** Let `m >= 2`, and let `X ∈ GL_m(F_q)` be non-scalar.
- A line is fixed by `X` iff it lies in an eigenspace `E_λ = ker(X - λ)`, `λ ∈ F_q^x`. The `E_λ`
  are independent, so their dimensions satisfy `Σ d_λ <= m`, and `d_λ <= m - 1` because `X` is not
  scalar.
- A `d`-dimensional space has `(q^d - 1)/(q - 1)` lines, and `F_q^m` has `(q^m - 1)/(q - 1)`. So
  `fpr(X) <= Σ_λ (q^(d_λ) - 1) / (q^m - 1)`.
- `f(d) = q^d - 1` is convex with `f(0) = 0`, so `f(a) + f(b) <= f(a + b)`. Merging parts only
  increases the sum, so under the constraints the sum is at most `f(m - 1) + f(1) = q^(m-1) + q - 2`.
- For `q = 2` only `λ = 1` occurs, and `fpr(X) <= (2^(m-1) - 1)/(2^m - 1) < 1/2`.
- For `q >= 3`, `q^(m-1) + q - 2 <= (q^m - 1)/2` iff `q^(m-1)(q - 2) >= 2q - 3`, and
  `q^(m-1)(q - 2) - (2q - 3) >= q(q - 2) - (2q - 3) = (q - 1)(q - 3) >= 0`.
- So every nontrivial element of `PGL_m(F_q)` fixes at most half of the points of `P^(m-1)(F_q)`.

**Corollary 1 (finitely presented ⇒ residually finite).** Let `G = <S | R>` with `S` finite and
relators of length at most `L`, and let `r >= L`. By the theorem there is an injective partial
homomorphism `φ` from the ball `B(r)` (containing `e` and `S^(±1)`) into a finite group `Q`.
- Define `ψ` on the free group by `ψ(s) = φ(s)`. Since `φ(s) φ(s^(-1)) = φ(e) = 1`,
  `ψ(s^(-1)) = φ(s^(-1))`.
- For a word `w` of length at most `r`, each prefix represents an element of `B(r)`, and partial
  multiplicativity along prefixes gives `ψ(w) = φ(w̄)`, where `w̄ ∈ G` is the element `w` represents.
- Each relator has length at most `L <= r` and represents `e`, so `ψ` kills it. So `ψ` induces a
  homomorphism `G -> Q` that agrees with `φ` on `B(r)` and is injective there. As `r` is arbitrary,
  `G` is residually finite.

**Corollary 2.** Let `S` be finitely presented, infinite and simple, with relators of length at most
`L`, and let `σ_N` be a sofic approximation.
- Suppose that for infinitely many `N` every defect `σ_N(gh)^(-1) σ_N(g) σ_N(h)` with
  `g, h ∈ B(L)` is trivial. For such `N`, the argument of Corollary 1 (with `σ_N|B(L)` in place of
  `φ`; injectivity is not needed) gives a homomorphism `ψ_N : S -> Sym(Ω_N)` agreeing with `σ_N` on
  the generators.
- For large `N`, `σ_N(s) ≠ 1` for a generator `s ≠ e`, so `ψ_N` is nontrivial. Since `S` is simple,
  `ψ_N` is injective, and `S` is finite, a contradiction.
- So for all large `N` some defect on `B(L)` is nontrivial. There are finitely many pairs, so the
  fixed-point ratio of that defect tends to `1`. By the theorem's first step it cannot lie in a
  family with a gap, so the gap families (A) and (P) are excluded.

**Corollaries 3 and 4** are Corollary 2 applied to `EL_n(R)/Z`, and the theorem's first step applied
to `GL_(3N)(F_2)` acting on `F_2^(3N)`, which lies in family (A).
