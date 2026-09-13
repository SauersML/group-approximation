---
rg: 2
id: ln-completion-word-problem-reduction-proof
kind: route
title: Push t-letters right through the covariance relation, annihilate against s-letters, and count the blow-up
requires:
  - leavitt-nekrashevych-completion-embeds-and-is-fp
  - no-fp-simple-algebra-hosts-every-decidable-algebra
target: ln-completion-word-problem-reduces-to-base-algebra
---

Notation as in the claim. `ψ^λ` denotes the `λ`-fold iterate, a homomorphism
`B -> M_{d^λ}(B)` indexed by words of length `λ`, with
`ψ^{λ+1}(b)_{(αi),(βj)} = ψ(ψ^λ(b)_{αβ})_{ij}`.

## 0. Three rewriting identities in O_ψ

From the covariance relation `b = Σ_{a,e} s_a ψ(b)_{ae} t_e` and `t_i s_j = δ_{ij}`:

- **(R1)** `t_i s_j = δ_{ij}`;
- **(R2)** `t_i b = Σ_e ψ(b)_{ie} t_e`, since `t_i b = Σ_{a,e} t_i s_a ψ(b)_{ae} t_e`;
- iterating (R2): `t_ρ b = Σ_{|ρ'|=λ} ψ^λ(b)_{ρρ'} t_{ρ'}` for `|ρ| = λ`.

Here `t_ρ = t_{ρ_1} ... t_{ρ_λ}` and `s_ν = s_{ν_1} ... s_{ν_λ}`. The Leavitt relation
iterates to `Σ_{|μ|=M} s_μ t_μ = 1` for every `M >= 0`.

## 1. Grading

Every defining relator of `O_ψ` (the relators of `B`, the Leavitt relators and the
covariance relators) is homogeneous of degree `0` for `deg s_i = 1`,
`deg t_i = -1`, `deg g = 0`. So `O_ψ = ⊕_k O_k`, and an element is zero iff each
homogeneous component is zero.

## 2. The procedure for one monomial

Let `u = x_1 ... x_r` be a monomial of degree `k`, `r <= l`, with letters in
`{g_k, s_i, t_i}`. Put `N = l`, and fix `μ, ν` with `|μ| = N + k >= 0`, `|ν| = N`.
Maintain an expression `E = Σ_{|ρ|=λ} b_ρ t_ρ` with `b_ρ in K<g>`. Start with
`λ = N + k` and `b_ρ = δ_{ρμ}`, so `E = t_μ`. For each letter `x_p` in turn:

- `x_p = g`: replace `b_{ρ'}` by `Σ_ρ b_ρ ψ^λ(g)_{ρρ'}`, by (R2) iterated;
- `x_p = t_i`: replace `ρ` by `ρi` and `λ` by `λ + 1`;
- `x_p = s_i`: keep only the terms with `ρ_λ = i`, drop the last letter of `ρ`, and
  replace `λ` by `λ - 1`, by (R1).

At a letter `s_i`, `λ = N + #s(x_p..x_r) - #t(x_p..x_r) >= N + 1 - r >= 1`, so the
step is defined. After the last letter, `λ = N + k - k = N`. Then
`t_ρ s_ν = Π_j δ_{ρ_j, ν_{N+1-j}}` by (R1). So `t_μ u s_ν` equals, in `O_ψ`, the
image of the polynomial `Y_{μν}(u) := b_{ν^rev}`, where `ν^rev` is `ν` reversed.
For a polynomial, `Y_{μν}` is extended linearly.

## 3. Correctness of the reduction

Let `w_k` be the degree-`k` part of the expansion of `w`. Using
`Σ_{|μ|=l+k} s_μ t_μ = 1 = Σ_{|ν|=l} s_ν t_ν`,

`w_k = Σ_{μ,ν} s_μ (t_μ w_k s_ν) t_ν = Σ_{μ,ν} s_μ Y_{μν}(w_k) t_ν` in `O_ψ`.

If all `Y_{μν}(w_k)` vanish in `B`, then `w_k = 0`. Conversely, if `w_k = 0` then
`t_μ w_k s_ν = 0` in `O_ψ`. This element is the image of `Y_{μν}(w_k) in B`, and
`B -> O_ψ` is injective because `ψ` is (`leavitt-nekrashevych-completion-embeds-and-is-fp`,
part 2), so `Y_{μν}(w_k) = 0` in `B`. By section 1, `w = 0` iff every `w_k = 0`.
This proves part 1 apart from the size bounds.

## 4. Size bounds

Throughout the procedure `λ <= (N + k) + #t(u) <= 3l`. Let `mon_j` be the maximum
number of monomials of an entry of `ψ^j(g)` over generators `g`, and `deg_j` the
maximum degree. Then `deg_j <= D^j`. Applying `ψ` to a monomial of degree `q` gives
entries with at most `d^{q-1} c^q <= (dc)^q` monomials, so
`mon_{j+1} <= mon_j (dc)^{D^j}` and `mon_j <= (dc)^{j D^j}`.

Each generator step multiplies the `b`'s by entries of some `ψ^λ(g)` and sums over
at most `d^λ <= d^{3l}` indices. After at most `r <= l` generator steps, each
`b_ρ` is a sum of at most `d^{3l^2}` products of at most `l` entries of iterates
`ψ^j(g)` with `j <= 3l`. So it has degree at most `l D^{3l}` and at most
`d^{3l^2} (dc)^{3 l^2 D^{3l}}` monomials.

An expression of length `l` expands into at most `2^l` monomials, since a product of
polynomials with `Σ m_i <= l` letters has at most `Π m_i <= 2^l` monomials. So
`Y_{μν}(w_k)` has at most `2^l d^{3l^2} (dc)^{3l^2 D^{3l}} <= (dc)^{8 l^2 D^{3l}}`
monomials, using `dc >= 2`. This proves part 1.

## 5. Running time (part 2)

The number of pairs `(μ, ν)` is at most `d^{3l}` for each of at most `2l + 1`
degrees. The procedure performs at most `S(l) = (dc)^{c_0 l^2 D^{3l}}` field
operations and index manipulations for an absolute `c_0`, on coefficients starting
from the codes of the coefficients of `w` and of the `p_{k,ij}`.

For a computable field, let `E_K(n)` be the maximum, over codes `<= n`, of the codes
of the results of `+, -, ×` and of the running times of these operations and of the
equality test. `E_K` is recursive. After `M` operations from inputs with codes
`<= n`, all codes are at most `E_K^{(M)}(n)` and the total time is at most
`M E_K^{(M)}(n)`. Put `T_K(x) = max_{y <= x} G(y)` with `G(y) = S_y E_K^{(S_y)}(y)`,
where `S_y = 2^{2^{y}}`. `T_K` is recursive and nondecreasing, and
`S(l) <= 2^{2^{C l}}` for `C` depending on `d, D, c`. Enlarging `C` to absorb the
coefficient codes gives the computation time `T_K(C l)`. There are at most
`T_K(C l)` zero tests in `B`, each on an input of size at most `T_K(C l)`. This
proves part 2.

## 6. Free bases (part 3)

For a free algebra, the zero test collects like terms, which is part of the
field-operation count above. So `F_B` is absorbed, and every `O_ψ` over a free base
solves its word problem on expressions of length `l` in time `T'_K(C l)` for one
recursive `T'_K` depending only on `K`, where `C` depends on the completion. This
is the hypothesis of `no-fp-simple-algebra-hosts-every-decidable-algebra` for the
class `H_free` with `T = T'_K`. That theorem gives a decidable `X` with `A_X`
embedding in no member of `H_free`. The same argument applies to any base class
whose polynomial zero tests share one recursive bound, for example commutative
polynomial rings `K[t_1..t_k]`, where zero testing is again collecting terms.

## 7. Part 4

Parts 2 and 3 do not use ψ-minimality or aperiodicity. So any recursion over a free
base, in particular every transducer recursion of Attempt 3 of
`decidable-algebras-embed-in-simple-ln-completions`, lies in `H_free`. Some
decidable `A_X` then embeds in none of them. For a hosting completion, the word
problem of `B` on polynomials must exceed every shared recursive bound as the
input varies. That complexity has to come from the relators of `B`.
