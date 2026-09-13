# Depth growth of binary Leavitt units: free-group leading terms, triangular units, squaring screens

Lane `ex-q34-unit-depth`, 2026-09-13. Target: `leavitt-units-of-infinite-order-have-linear-depth-growth`.

Notation. `R = L_(F_2)(1,2)`, `Q = R^x`. For words `μ = μ_1...μ_k` put `s_μ = s_(μ_1)...s_(μ_k)` and
`t_μ = t_(μ_k)...t_(μ_1)`, so `t_μ s_μ = 1`. The normal-form monomials `s_μ t_ν` (with `μ, ν` not both ending
in `1`) form a basis. `R_N = span{ s_μ t_ν : |μ|, |ν| <= N }`, `ell(x) = min{ N : x in R_N }`,
`D_u(m) = max(ell(u^m), ell(u^-m))`, `lambda(u) = lim D_u(m)/m`. `X = {0,1}^N` is the Cantor set, and
`D = span{ s_w t_w }`, which is the algebra of locally constant functions `X -> F_2` (`s_w t_w = 1_[w]`).

## 1. The free-group grading

Let `F` be the free group on `x_0, x_1`. Put `deg s_i = x_i` and `deg t_i = x_i^(-1)`. Both defining relations
are homogeneous (`t_i s_j` has degree `x_i^(-1) x_j`, which is `1` when `i = j`, and `s_i t_i` has degree `1`).
So `R = ⊕_(g in F) R_g` with `R_g R_h <= R_(gh)`, and every normal-form monomial is homogeneous:
`deg s_μ t_ν = x_μ x_ν^(-1)`.

**Facts.**
- (1a) `R_g != 0` only if `g = x_μ x_ν^(-1)` for positive words `μ, ν`. Choose them without a common last
  letter. Then `R_g = s_μ D t_ν`, and every `y in R_g` is `s_μ f t_ν` for a unique `f in D`, namely
  `f = t_μ y s_ν`. In particular `R_1 = D`.
- (1b) Depth bounds support length. If `x in R_N` and `x_g != 0`, then `|g| <= 2N`, where `|g|` is the free
  length. Indeed `x_g` is a sum of the monomials of `x` of degree `g`, each of which has `|μ|, |ν| <= N`.

**Lemma 1 (leading term).** Let `<` be a bi-invariant order on `F` (free groups are bi-orderable). For `x in R`
let `g` be the `<`-largest element of `supp(x) = { h : x_h != 0 }`. Then `(x^m)_(g^m) = (x_g)^m` for all `m >= 1`.

*Proof.* `(x^m)_(g^m) = Σ x_(h_1) ... x_(h_m)` over `h_1 ... h_m = g^m` with every `h_i` in `supp(x)`. Since
`h_i <= g` and the order is bi-invariant, `h_1 ... h_m <= g^m`, with equality only if every `h_i = g`. ∎

**Lemma 2 (persistence).** Let `y = s_μ 1_E t_ν in R_g`, where `E` is a nonempty clopen set and `μ, ν` have no
common last letter.
- (i) If `μ` and `ν` are incomparable (neither is a prefix of the other), then `y^2 = 0`.
- (ii) If `μ = νγ` or `ν = μγ` with `γ` nonempty, then `y` is nilpotent iff the periodic point `γ^∞` is not in `E`.

*Proof.*
- (i) `t_ν s_μ = 0`.
- (ii), case `μ = νγ`. `y^m = s_ν (s_γ 1_E)^m t_ν`. Since `s_γ f = θ(f) s_γ` with `θ(f) = s_γ f t_γ = 1_(γE)`,
  one gets `(s_γ 1_E)^m = 1_(E_m) s_γ^m` with `E_m = γE ∩ γ^2 E ∩ ... ∩ γ^m E`.
- `E_m <= [γ^m]`, and multiplying `s_ν 1_(E_m) s_γ^m t_ν` by `t_ν` on the left and `s_ν t_γ^m` on the right
  returns `1_(E_m)`. So `y^m != 0` iff `E_m` is nonempty.
- `γ^m w` lies in `E_m` iff `w, γw, ..., γ^(m-1) w` all lie in `E`.
  - If `γ^∞ in E`, then `w = γ^∞` works for every `m`.
  - If not, some cylinder `[γ^j]` misses `E`. For `m > j` the point `γ^(m-1) w` lies in `[γ^j]`, so `E_m` is empty.
- Case `ν = μγ`. The involution `s_μ t_ν -> s_ν t_μ` is an anti-automorphism fixing `D` pointwise. It sends
  `y` to `s_ν 1_E t_μ`, which is the first case, and `y` is nilpotent iff `y*` is. ∎

**Proposition 3 (leading-term criterion).** Let `u in Q` and `k >= 1`, and let `<` be a bi-invariant order on
`F`. Suppose the `<`-largest element `g = x_μ x_ν^(-1)` of `supp(u^k)` is not `1`, that `μ` and `ν` are
comparable, and that the periodic point `γ^∞` of Lemma 2(ii) lies in the coefficient set `E` of `(u^k)_g`.
Then `lambda(u) >= 1/(2k)`.

*Proof.* By Lemmas 1 and 2, `(u^(km))_(g^m) = ((u^k)_g)^m != 0`. So `g^m` lies in `supp(u^(km))`, and by
(1b) `ell(u^(km)) >= |g^m|/2 >= m/2`, because `|g^m| >= m` for `g != 1` in a free group. Hence
`D_u(km) >= m/2` and `lambda(u) >= 1/(2k)`. ∎

**Reading.** Suppose `lambda(u) = 0`, as for a Heisenberg center. Then for every bi-invariant order and every
power `u^k`, the leading coefficient of `u^k` is nilpotent. It is either an incomparable pair, the shape of a
transvection `1 + s_0 t_1`, or a comparable pair whose coefficient set misses its periodic point.
The `Z`-grading is the image of this grading under `x_i -> 1`. The extreme-component remark on the target
claim is the analogous statement for whole `Z`-components.

## 2. Triangular units

Let `R_(<=0) = ⊕_(k <= 0) R_k` in the `Z`-grading (`deg s_i = 1`, `deg t_i = -1`), and
`H_<= = { u in Q : u, u^(-1) in R_(<=0) }`. This is the group `H^1_<=` of
`research/artifacts/depth-monotone-leavitt-firewall-2026-09-12.md`, which contains every level transvection,
every depth-decreasing transvection and the level part of `V`. Define `H_>=` in the same way.

**Proposition 4.** Every `u` of infinite order that is conjugate in `Q` into `H_<=` or `H_>=` satisfies
`lambda(u) >= 1/r > 0`, where `r` is the order of the degree-zero component `u_0`.

*Proof.*
- `lambda` is a conjugacy invariant: `D_(huh^(-1))(m) <= D_u(m) + 2 max(ell(h), ell(h^(-1)))`. So take `u` in
  `H_<=`. The case `H_>=` follows by applying the involution, which preserves `ell`.
- `x -> x_0` is a ring map `R_(<=0) -> R_0`. So `u_0` is a unit of `R_0 = ⋃_n M_(2^n)(F_2)`, and it has a finite
  order `r`.
- `v = u^r` has `v_0 = 1`, so `v = 1 + n` with `n in R_(<0)`. In characteristic two, `v^(2^k) = 1 + n^(2^k)`.
- `u` has infinite order, so `v^(2^k) != 1`, and `n^(2^k)` is a nonzero element of `R_(<= -2^k)`. Each of its
  monomials `s_μ t_ν` has `|ν| >= 2^k`. So `ell(v^(2^k)) >= 2^k`.
- `D_v` is subadditive with limit `lambda(v)`, and `D_v(2^k) >= 2^k`. So `lambda(v) >= 1`, and
  `lambda(u) = lambda(v)/r >= 1/r`. ∎

## 3. Bounded degree range

Suppose `u` has infinite order and every `u^m`, `m in Z`, has `Z`-degrees in `[-D, D]`. Put
`A = F_2[u^(+-1)]`, a Laurent polynomial ring contained in `⊕_(|k| <= D) R_k`. Then
`A ∩ R_(>=0) = A ∩ R_(<=0) = F_2`. The proof is on the target claim's Attempts. So every nonconstant element of
`A` has components of both signs, and a bounded-degree counterexample must raise its spatial resolution without
raising its lag.

## 4. Squaring screens (exact, MSI)

Script: `research/artifacts/leavitt-unit-squaring-screen-2026-09-13.py`. It uses `leavitt.py` of
`experiments/nonsofic-certificates/`, with dual-path checking off.
- **Generators.** Thirteen units and their inverses. The Thompson units `A, B, C, P` are those of
  `research/artifacts/leavitt-unit-depth-growth-experiment-2026-09-12.md`. The transvections are `1 + n` for
  `n` in `S[0]T[10]`, `S[10]T[0]`, `S[0]T[1]`, `S[0]T[11]`, `S[11]T[0]`, `S[0]T[100]`, `S[100]T[0]`,
  `S[01]T[1]` and `S[1]T[01]`.
- **Method.** For a random word `u`, compute `u^(2^k)` and `u^(-2^k)` by repeated squaring, recording depth,
  degree range and monomial count. A run stops when:
  - a square is `1` (FIN2, a 2-power order);
  - a square repeats an earlier square (REP, finite order);
  - a factor exceeds the monomial cap (CAP);
  - or after `K` squarings (OK).
- **Flag.** SLOW is set when the last three recorded squarings each add at most 2 to the depth. A
  self-similar unit with `u^2` conjugate to `phi(u)` would set it.

| run | seeds | draws per seed | word length | `K` | cap | CAP | OK | FIN2 | REP |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 1–4 | 400 | 2–12 | 10 | 1200 | 1296 | 104 | 103 | 61 |
| 2 | 11–16 | 700 | 2–16 | 12 | 2000 | 3614 | 179 | 209 | 102 |

Counts are of distinct units within a seed.
- **SLOW.** In run 2, 2322 units were followed through at least three squarings without a detected finite order.
  None set SLOW. The smallest ratio `D(2^K)/2^K` observed was `0.501`, for the word `ACB`, with depths
  `3,3,4,6,10,18,34,...,1026`.
- **Affine doubling.** Every followed unit shows eventually affine doubling, `D(2^(k+1)) = 2 D(2^k) - c` with
  `c in {1,2}`. This is the signature of a positive translation length.

**Reading.** In both screens no sampled unit has sublinear depth growth. Short words in these generators do not
produce self-similar squaring. This is evidence only. The screens do not reach units designed to cancel every
leading term of Proposition 3.
