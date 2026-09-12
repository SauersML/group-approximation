# Independent review: strict comparison compares projections in the tracial ultrapower

Reviewer lane `reviewer`, 2026-09-12. The coordinator requested an adversarial review of `strict-comparison-compares-ultrapower-projections` and its route `strict-comparison-compares-ultrapower-projections-proof`. The proof is Section 1 of `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md`, landed in 341ea56ac. The focus was Steps 4–6 and the diagonal argument.

## Verdict

| item | verdict |
| --- | --- |
| Theorem, Steps 1–6 | **PASS** |
| equality clause (`p ~ q` when all limit traces agree) | **PASS** |
| "in particular" clause for the uniform tracial completion | **PASS**, conditional on the CCEGSTW embedding being the diagonal one |
| Consequence 2.1 (Toms's certificates force failure of strict comparison) | **plausible, not reviewed**; see Section 3 |
| Consequence 2.2 (`(Q_tr)` plus CETW Theorem A gives unital Toms–Winter) | **PASS** as logic |

The theorem is correct as stated. Its standard inputs are Glimm's lemma, Rørdam's lemma and Haagerup's theorem that quasitraces on exact algebras are traces. Each is stated correctly and none was re-read here. The novelty disclaimer on the node is appropriate.

## 1. Steps 1–3

- **Lifts.** Clipping a self-adjoint lift with `f(t) = min(max(t,0),1)` represents `f(p) = p`, because the quotient `l^∞(M_k(A)) → M_k(A^ω)` is a *-homomorphism.
- **`ε_n → 0`.** `a_n − a_n²` is positive and represents `p − p² = 0`. By Cauchy–Schwarz with unnormalized `Tr_k`, `τ(x) ≤ k^(1/2) ||x||_(2,τ)` for positive `x`.
- **`η_n → 0`.** Limit traces are well defined on `M_k(A^ω)`, since `|τ(x)| ≤ k^(1/2)||x||_(2,τ)` kills the null ideal. Choosing near-maximizing `τ_n` on an `ω`-large set gives a limit trace with `σ(p) − σ(q) >= c/2`. Correct.
- **Spectral inequalities.**
  - `1_(1/2,1](t) <= t + 2t(1−t)` holds on `[1/2,1]`, because `3t − 2t² − 1 = −(2t−1)(t−1) >= 0` there.
  - `t <= 1_(1/2,1](t) + 2t(1−t)` on `[0,1/2]` is equivalent to `t <= 1/2`.
  - `t <= 1_(δ,1](t) + δ` is immediate.
  - With `d_τ((x−e)_+) = τ(1_(e,1](x))` in the GNS von Neumann algebra, the three rank bounds follow, and `j δ` comes from `Tr_j(1) = j`.
- **Glimm witness.**
  - A unital simple infinite-dimensional algebra is not type I, so Glimm's lemma applies.
  - The `l` orthogonal Cuntz-equivalent copies of `c_l` give `l·d_τ(c_l) <= d_τ(1) = 1`.
  - Faithfulness of traces on simple `A` and weak* compactness of `T(A)` give `m_l > 0`.
  - `d_τ((c_l − δ_l)_+) >= τ(c_l) − δ_l >= 3m_l/4`. Correct.

## 2. Steps 4–6, line by line

**Step 4.**
- **The rank inequality.**
  - `d_τ(a') <= τ(a_n) + 2τ(a_n − a_n²) <= τ(b_n) + η_n + 2ε_n`, by the definitions of `η_n` and `ε_n`.
  - `d_τ(b') = d_τ((b_n − 1/2)_+) + d_τ((c_l − δ_l)_+) >= τ(b_n) − 2ε_n + 3m_l/4`.
  - The strict middle inequality needs `η_n + 4ε_n < 3m_l/4`, and the step assumes `< m_l/2`. The margin is uniform in `τ`, so `d_τ(a') < d_τ(b')` for **every** `τ`. Correct.
- **Strict comparison.** It gives `a' ≾ b'` in `M_∞(A)`. Both elements lie in `M_(k+1)(A)`, and compressing the implementing elements by `1_(k+1)` keeps the subequivalence inside `M_(k+1)(A)`.
- **Rørdam's lemma.** `a ≾ b` iff for every `e > 0` there is `s` with `(a−e)_+ = s* b s` (Kirchberg–Rørdam 2000, Lemma 2.2). With `e = 1/4`, `((a_n − 1/2)_+ − 1/4)_+ = (a_n − 3/4)_+`. Correct.
- **The element `x = b'^(1/2) s`.** `x*x = s*b's`, and `||x||² = ||(a_n − 3/4)_+|| <= 1/4`. `xx* = b'^(1/2) ss* b'^(1/2)` lies in `her(b')`. Correct.

**Step 5.**
- **`x = xe`.** `x*x` is supported under `e`, so `(1−e)x*x(1−e) = 0`, hence `x(1−e) = 0`.
- **`w*w`.** `w = ex`, and `w*w = x*ex = x*x − x*(1−e)x`.
- **Where `z` lives.** `b' = b_1 ⊕ b_2` commutes with `e`. So `(1−e) b' y b' (1−e) = (0 ⊕ b_2) y (0 ⊕ b_2)`, and by continuity `(1−e) her(b') (1−e) ⊆ her(b_2) = her((c_l − δ_l)_+) ⊆ her(c_l)`.
- **The trace of `z`.** `τ(x*(1−e)x) = τ(yy*)` with `y = (1−e)x`, which equals `τ(z) <= ||z|| d_τ(z) <= (1/4) d_τ(c_l) <= 1/(4l)`. Correct, uniformly in `τ`.
- **The cut-off `g`.** `g(b_n)(b_n − 1/2)_+ = (b_n − 1/2)_+`, so `g(b_n)` acts as the unit on `her((b_n − 1/2)_+)`. `exx*e` is the `(1,1)` corner of an element of `her(b')`, so it lies in `her((b_n−1/2)_+)`. Hence `ww* = g(b_n) ww* g(b_n)`. Correct.

**Step 6, the diagonal argument.**
- **Index sets.** `S_l ∈ ω` because `η_n + 4ε_n → 0` along `ω` and `m_l > 0`, so `T_l ∈ ω`.
- **Choice of `l(n)`.** For `n ∈ T_1`, `l(n) = max{l <= n : n ∈ T_l}` is well defined. On `T_L ∩ [L,∞) ∈ ω` it is `>= L`, so `lim_ω l(n) = ∞`.
- **Step 4 applies at every index.** `n ∈ T_(l(n)) ⊆ S_(l(n))`, so the hypothesis holds at `(l(n), n)`. This is the point where a diagonal argument usually fails, and it holds here.
- **Boundedness.** `||w_n|| <= 1/2`, so `[(w_n)] ∈ M_k(A^ω)`.
- **Error term.** `||x_n*(1−e)x_n||²_(2,τ) <= ||x_n*(1−e)x_n|| · τ(x_n*(1−e)x_n) <= 1/(16 l(n))`, uniformly in `τ`. It tends to `0` along `ω`.
- **Identities in the ultrapower.**
  - `w*w = [(a_n − 3/4)_+] = (p − 3/4)_+ = p/4`, since functional calculus commutes with the quotient.
  - `ww* = g(q) ww* g(q) = q ww* q`, since `g(q) = q`.
- **The partial isometry.** `v = 2w` has `v*v = p`, so `vv*` is a projection in `q M_k(A^ω) q`, i.e. `vv* <= q`. Correct.

**Equality clause.** `q − vv*` is a projection whose limit traces are all `0`. Represent it by positive contractions `y_n`. `sup_τ τ(y_n − y_n²) → 0`, so `||y_n||²_(2,τ) <= τ(y_n) + o(1)`, and the Step 1 compactness argument makes it `0`. Correct.

## 3. Hidden hypotheses and scope

- **What is actually used.** Strict comparison over `T(A)`, which exactness makes equal to comparison over quasitraces, together with unital, simple and non-elementary. Nuclearity, CPoU, Gamma and dimension hypotheses are all unused, as the node says.
- **Known-case test.** For `Z`-stable nuclear `A`, CPoU gives the same conclusion (CCEGSTW Theorem 7.17), so there is no conflict. For Villadsen or Toms algebras without strict comparison the theorem says nothing, so again no conflict.
- **The "in particular" clause.** It uses the CCEGSTW embedding `M ↪ A^ω`. It holds provided that embedding is the diagonal one, under which a limit trace restricted to `M` is `lim_ω τ_n|_M` with `τ_n ∈ T(A)`. That is the standard construction, not re-read here.
- **Consequence 2.1 (Toms's certificate, simple `B`).** It depends on the internal structure of Toms's Theorems 2 and 5. The claim is that a partial isometry in `M_k(B^ω)` supplies finite-stage 2-norm approximants just as one in `M_k(M)` does. Along `ω` it supplies, for each large index, an element close to a partial isometry from `P` to `Q`, which is what a fixed-threshold finite-stage argument needs. That is plausible, but the reviewer did not read Toms Section 6, so **no verdict** on 2.1. The node's distinct_from cites `toms-gamma-counterexample-fails-strict-comparison`, which reaches the same conclusion by a different route, so nothing in the graph currently rests on 2.1 alone.
