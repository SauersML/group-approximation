# Referee report (gq-referee-c): leavitt-resolvent-ring-is-fp-simple-of-char-zero

- **Node:** `research/leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`, landed aaf4b1279 by lane
  `gq-ring-fp-simple`.
- **Lens:** an independent proof of simplicity that does not use the `O_ψ` criterion, plus calibration of
  each relation.
- **Verdict: PASS.** `R_L` is nonzero, a `Q`-algebra with `Q ⊆ R_L` unital, and simple. Clause 3
  (`M_n(R_L) ≅ R_L`, and `GL_n(Q) ≤ [R^x, R^x]` via the perfect `SL_(n+2)(Q)`) is also correct.

Throughout, `R = R_L = Z<s_1,s_2,t_1,t_2,N,A | t_i s_j = δ_ij, s_1t_1 + s_2t_2 = 1, N s_1 = s_1(N+1),
N s_2 = 0, A(N+1) = 1 = (N+1)A>`. For a word `μ = μ_1…μ_k` write `s_μ = s_(μ_1)…s_(μ_k)` and
`t_μ = t_(μ_k)…t_(μ_1)`, so `t_μ s_ν = δ_μν` for `|μ| = |ν|`.

## 1. Consequences of the relations

1. **`t_1 N = (N+1) t_1` and `t_2 N = 0`.** Expand `t_i N = t_i N (s_1 t_1 + s_2 t_2)` and use `N s_1 = s_1(N+1)`,
   `N s_2 = 0`.
2. **`(N+c)^(-1) = t_1^(c-1) A s_1^(c-1)` for every `c >= 1`, two-sided.** From 1, `(N+c) t_1^(c-1) = t_1^(c-1)(N+1)`.
   From the shift relation, `s_1^(c-1)(N+c) = (N+1) s_1^(c-1)`. Then use `A(N+1) = 1 = (N+1)A`.
3. **`1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`.** `(N+1) s_1^(m-1) s_2 = s_1^(m-1)(N+m) s_2 = m s_1^(m-1) s_2`, so
   `s_1^(m-1)s_2 = m A s_1^(m-1) s_2`. Now apply `t_2 t_1^(m-1)` on the left. `m` is central, so `R` is a
   `Q`-algebra and `Q` is central.
4. **Commutation with B.** Let `B = Q[N][(N+c)^(-1) : c >= 1] ⊂ Q(N)`. The universal property of localization
   gives a ring map `B -> R`. For every `f ∈ B`:
   - `f s_1 = s_1 f(N+1)` and `f s_2 = s_2 f(0)`;
   - `t_1 f = f(N+1) t_1` and `t_2 f = f(0) t_2`.

   Check these on `N` and on `(N+c)^(-1)`; they are multiplicative. For example `(N+c) s_2 = c s_2` gives
   `(N+c)^(-1) s_2 = s_2/c`. Every `f ∈ B` is defined at every integer `k >= 0`.
5. **Spanning set.** `R` is spanned by the terms `s_μ f t_ν` with `f ∈ B`. By 4 this span is closed under left
   multiplication by each generator, and it contains `1`.
6. **Lengthening.** `s_μ f t_ν = s_(μ1) f(N+1) t_(ν1) + s_(μ2) f(0) t_(ν2)`, since `f = f(s_1t_1 + s_2t_2)`.
   It preserves the **degree** `|μ| - |ν|` of a term.

## 2. R ≠ 0

On `Q^(X)`, with `X` the words that are tail-equivalent to `2^∞`, set:
- `s_i e_ξ = e_(iξ)`, `t_i e_(iξ) = e_ξ` and `t_i e_(jξ) = 0` for `j ≠ i`;
- `N e_ξ = ℓ(ξ) e_ξ`, where `ℓ(ξ)` is the number of leading 1's of `ξ`;
- `A = (N+1)^(-1)`.

All nine relations hold: `ℓ(1ξ) = ℓ(ξ) + 1`, `ℓ(2ξ) = 0`, and `N + 1 >= 1` on every basis vector. So `1 ≠ 0`
in `R`, and every nonzero rational number is a unit of `R`.

## 3. Simplicity, without the O_ψ criterion

Let `I ≠ 0` be a two-sided ideal and let `0 ≠ x ∈ I`. Write `x` as a finite sum of terms, and let `x_d` be the
sum of its terms of degree `d`. Some `x_(d_0) ≠ 0`.

**Step 1: isolate one nonzero coefficient.**
- Lengthen the terms of `x_(d_0)` until every one has `|ν| = K`, and collect them:
  `x_(d_0) = Σ_(|μ|=K+d_0, |ν|=K) s_μ g_μν t_ν` with `g_μν ∈ B`.
- Since `x_(d_0) ≠ 0`, some coefficient `f := g_(μ_0 ν_0)` is a nonzero element of `B`.
- Put `x' = t_(μ_0) x s_(ν_0) ∈ I`. Words of equal length satisfy `t_(μ_0) s_μ = δ` and `t_ν s_(ν_0) = δ`, so
  `t_(μ_0) x_(d_0) s_(ν_0) = f`.
- The commutation rules of §1 are degree-homogeneous. So each other part `x_d` becomes a finite sum `y_e` of
  terms of degree `e = d - d_0 ≠ 0`.
- Hence `x' = f + Σ_(e≠0) y_e`.

**Step 2: compress along an aperiodic word.**
- Let `D` be the largest `|e|` that occurs and `K_0` the longest word in any term of any `y_e`.
- Choose `k >= 0` with `f(k) ≠ 0`. A nonzero rational function has finitely many zeros, and `f` has no poles at
  `k >= 0`.
- Let `γ = 1^k 2 2^Z 1^T 2` with `T > D` and `Z` large enough that `|γ| > K_0 + T + 1`.

*Degree 0.*
- `t_γ f s_γ = t_β t_2 (t_1^k f s_1^k) s_2 s_β`, where `γ = 1^k 2 β`.
- `t_1^k f s_1^k = f(N+k)`, and `f(N+k) s_2 = s_2 f(k)`.
- So `t_γ f s_γ = f(k)`.

*A term `s_μ h t_ν` of degree `e > 0`.*
- It survives only if `γ = μγ' = νγ''`. Then `γ'' = wγ'` with `|w| = e`, and the term becomes
  `t_(γ') h s_(wγ') = t_(γ') s_(wγ') h̃`.
- This is nonzero only if `γ'` is a prefix of `wγ'`, that is, only if `γ'` is `e`-periodic.
- `γ'` is a suffix of `γ` of length `> T+1`. It ends in `2`, and the letter `e <= D < T` places before its end
  lies in the block `1^T`. So `γ'` is not `e`-periodic, and the term is `0`.

*Degree `e < 0`.* The same argument applies with `γ' = wγ''`: the term is `t_(wγ'') s_(γ'') ĥ`, which again
needs `γ''` to be `|e|`-periodic.

So `t_γ x' s_γ = f(k)`, a nonzero rational number and so a unit, and `1 ∈ I`. Hence `R` is simple. ∎

As a by-product, the model of §2 is faithful: its kernel is a proper ideal of the simple ring `R`.

## 4. Calibration: each relation is needed

In cases (i)–(iii) below, the ring obtained by dropping the relation has:
- a representation of characteristic `p`;
- the model of §2, which satisfies all the relations and has characteristic 0.

So `pR'` is a proper nonzero ideal, and `R'` is not simple.

- **(i) Drop the vacuum relation `N s_2 = 0`.** On `F_p(z)^(X)`, keep `s_i, t_i` as in §2 and set
  `N e_ξ = (z + ℓ(ξ)) e_ξ`. The shift relation holds, and `N + 1 = z + ℓ + 1` is invertible in `F_p(z)`. So the
  characteristic-0 mechanism (§1.3) needs the vacuum relation.
- **(ii) Drop the shift relation `N s_1 = s_1(N+1)`.** `N -> 0`, `A -> 1` maps `R'` onto `L_Z(1,2)`, which has
  the quotient `L_(F_p)(1,2) ≠ 0`.
- **(iii) Drop the resolvent `A`.** The integer model `N e_ξ = ℓ(ξ) mod p` on `F_p^(X)` satisfies the rest.
- **(iv) Drop `s_1 t_1 + s_2 t_2 = 1`.** This is the Toeplitz version. On the Fock space `Q^(finite words)`, with
  `N e_w = ℓ(w) e_w`, the element `P = 1 - s_1t_1 - s_2t_2` acts as the vacuum projection, which is nonzero. The
  quotient by `(P)` is `R_L ≠ 0`. So `(P)` is a proper nonzero ideal. This agrees with the node's
  `distinct_from` on the Toeplitz ring.

What the proof actually uses:
- both letters, for the aperiodic `γ`;
- the vacuum evaluation `f ↦ f(k)`, which lands in `Q`;
- the invertibility of all integers, which needs the shift, vacuum and resolvent relations together.

## 5. Comparison with the lane's proof

The lane's §§1–2 match §1 above. Its §4 (ψ-minimality) is the same evaluation `b ↦ b(k)`. Its §5
(aperiodicity) is the criterion-level version of Step 2. I found no error there, but this report does not rely
on it.

One remark: the node's "R ≠ 0" goes through `leavitt-nekrashevych-completion-embeds-and-is-fp`, while §2 above
gives it directly from the model.
