---
rg: 2
id: bounded-depth-symmetric-models-are-sofic-approximations-proof
kind: route
title: Young's rule and the hook formula give character ratio f^j + O(1/m) on depth-j constituents, which turns Hilbert-Schmidt relator defects into Hamming defects; simplicity of the finitary kernel and its trivial centralizer then upgrade a head-moving sofic trace to soficity
target: bounded-depth-symmetric-models-are-sofic-approximations
requires:
  - binary-jacobson-steinberg-cover-is-elementary
artifacts:
  - experiments/bounded-depth-symmetric-models-2026-09-18/check_char_asymptotic.py
  - experiments/bounded-depth-symmetric-models-2026-09-18/output.txt
---

Notation as on the target. `||A||_2^2 = tr(A*A)` is normalized, so for a unitary `U` of dimension `d`, with
`t = Tr U / d`, we have `min_{λ ∈ C} ||U - λ||_2^2 = 1 - |t|^2` and `||U - 1||_2^2 = 2 - 2 Re t`. On a direct sum
`⊕ U_i` with weights `p_i = dim_i / dim`, both `||·||_2^2` and `tr` are the `p`-weighted averages. `d_Ham(α,β)` is the
fraction of points where the permutations `α,β` differ, and `f(σ) = F(σ)/m = 1 - d_Ham(σ,1)`.

**Standard inputs (textbook; recalled, not quoted verbatim).** All are in Sagan, *The Symmetric Group*, 2nd ed.,
GTM 203, Chapters 2 and 3, and in James, LNM 682.
- (I) The complex irreducible representations of `Sym(m)` are the `S^λ`, `λ ⊢ m`, and `S^{λ'} ≅ sgn ⊗ S^λ`.
- (Y) Young's rule. `M^α = C[tabloids of shape α] ≅ ⊕_λ K_{λα} S^λ`, with Kostka numbers `K_{λα}` = the number
  of semistandard tableaux of shape `λ` and content `α`. `K_{αα} = 1`, and `K_{λα} ≠ 0` implies `λ ⊵ α`
  (dominance).
- (H) Hook length formula. `dim S^λ = m! / Π_{cells} hook`.

## Step 1. Fixed tabloids

Fix `j >= 1`, `ν ⊢ j` with `l` parts, and `m >= 4j`. Write `λ[ν] = (m-j, ν)`; it is a partition, since `ν_1 <= j <= m-j`.
A tabloid of shape `λ[ν]` is a tuple of disjoint subsets `(B_1, ..., B_l)`, with `|B_i| = ν_i`; the first row is the
complement. `σ` fixes it iff every `B_i` is a union of `σ`-cycles.

- *Main term.* The tuples with every `B_i ⊂ Fix(σ)` number `N_0 = F_(j) / Π ν_i!`, where `x_(j)` is the falling
  factorial.
- *Remainder.* The other fixed tuples use at least one cycle of length `>= 2`. Their union `B` is a `σ`-invariant set
  of size `j` made of `q <= j-1` cycles. There are at most `m^q` choices of the `q` cycles, and at most `l^q <= j^j`
  ways to distribute them among the blocks. So `N_1 <= j^{j+1} m^{j-1}`.
- `dim M^{λ[ν]} = m_(j) / Π ν_i!`, and `m_(j) >= (m/2)^j`.

Next, `F_(j)/m_(j) = Π_{i<j} (F-i)/(m-i)`. Each factor lies in `[-1,1]`, and
`|(F-i)/(m-i) - F/m| = i(m-F)/(m(m-i)) <= 2j/m`. A telescoping product bound gives `|F_(j)/m_(j) - f^j| <= 2j^2/m`.
Hence
```text
| χ_{M^{λ[ν]}}(σ) - f^j dim M^{λ[ν]} |  <=  E_j m^{j-1},      E_j = j^{j+1} + 2j^2 · j^j.        (1)
```
We used `dim M^{λ[ν]} <= m^j` and `N_1 + (dim M)|F_(j)/m_(j) - f^j| <= j^{j+1} m^{j-1} + m^j · 2j^2/m`.

## Step 2. Young's rule at fixed first row

By (Y), `M^{λ[ν]} = ⊕_{λ ⊵ λ[ν]} K_{λ,λ[ν]} S^λ`, and every `λ ⊵ λ[ν]` has `λ_1 >= m-j`.

- *First row exactly `m-j`.* Then `λ = (m-j, μ)` with `μ ⊢ j` and `μ ⊵ ν`. Moreover `K_{(m-j,μ),(m-j,ν)} = K_{μν}`. In
  a semistandard tableau of content `(m-j,ν)`, the `m-j` entries equal to `1` lie in row 1 (columns strictly increase),
  and they fill it, because row 1 has length `m-j`. Deleting row 1 and lowering every entry by one is a bijection onto
  semistandard tableaux of shape `μ` and content `ν`.
- *First row `m-i`, `i < j`.* These form `R_ν`. The partitions are `λ = (m-i, κ)`, `κ ⊢ i`, at most `Σ_{i<j} p(i) <= 2^j`
  of them. Each Kostka number is at most `j^j`: the `1`'s fill the first `m-j` cells of row 1, and the remaining `j`
  cells get the other entries. By (Y), `S^λ ⊂ M^λ`, so `dim S^{(m-i,κ)} <= m^i <= m^{j-1}`. Hence
  `dim R_ν <= G_j m^{j-1}`, with `G_j = 2^j j^j`.

## Step 3. Inversion

Put `d_μ = dim S^{(m-j,μ)}` and `x_μ = χ^{(m-j,μ)}(σ) - f^j d_μ`. Subtract `f^j` times the dimension identity from the
character identity of Step 2, and use (1) and `|χ_{R_ν}| <= dim R_ν`:
```text
| Σ_{μ ⊵ ν} K_{μν} x_μ |  <=  (E_j + 2 G_j) m^{j-1}      for every ν ⊢ j.                      (2)
```
The matrix `(K_{μν})_{μ,ν ⊢ j}` is integral and unitriangular for any linear order refining dominance, and it does
not depend on `m`. So its inverse is integral with entries bounded by some `H_j`, and
```text
|x_μ|  <=  p(j) H_j (E_j + 2G_j) m^{j-1}.                                                      (3)
```

## Step 4. Dimension lower bound

Take `λ = (m-j, μ)`. Its first-row cell in column `c` has hook `m - j - c + 1 + μ'_c`.
- For `c > μ_1` this is `m-j-c+1`. These hooks multiply to `(m-j-μ_1)!`.
- For `c <= μ_1` it is at most `m`.
- The hooks below row 1 are the hooks of `μ`, with product `H_μ <= j!`.

By (H), `d_μ >= m_(j+μ_1) / (m^{μ_1} j!) >= (m/2)^{j+μ_1} / (m^{μ_1} j!) >= m^j / (4^j j!)`, since
`m >= 4j >= 2(j+μ_1)`.

## Step 5. Lemma CA

Divide (3) by Step 4:
```text
| χ^{(m-j,μ)}(σ)/d_μ - f(σ)^j |  <=  C_j / m,     C_j = 4^j j! p(j) H_j (E_j + 2G_j).
```
By (I), the conjugate `(m-j,μ)'` has ratio `sgn(σ)` times this one. Put `C_D = max_{j<=D} C_j`. The numerical check in
the artifact computes characters by Murnaghan-Nakayama, independently of Steps 1-4. It finds `m·|r - f^j| <= 1.72`
for `j <= 3`, far below `C_j`.

For every constituent `S^λ` of `ρ_k` of dimension `> 1`, with `j = j(λ) ∈ [1,D]` its depth or conjugate depth, we get
```text
|r_λ(σ)|  <=  f(σ)^j + C_D/m  <=  f(σ) + C_D/m,
Re r_λ(σ)  >=  f(σ)^j - C_D/m  >=  1 - D(1 - f(σ)) - C_D/m      when sgn σ = 1.               (4)
```

## Step 6. Theorem A

**Hamming bound.** Fix `g,h`, put `δ = φ(gh)^{-1} φ(g) φ(h)` and `λ = c(gh) / (c(g)c(h))`, which has modulus one.
Since `ρ(φ(gh))` is unitary,
```text
def_{g,h}^2  =  ||ρ(δ) - λ||_2^2  =  Σ_i p_i ||ρ_i(δ) - λ||_2^2  >=  Σ_i p_i (1 - |t_i(δ)|^2),
```
where `ρ = ⊕ ρ_i` runs over the irreducible constituents with weights `p_i`, and `t_i` is the normalized character.
Keep only the constituents of dimension `> 1`, which have total weight `w`. For those, `|t_i| <= 1` and (4) give
`1 - |t_i|^2 >= 1 - |t_i| >= 1 - f(δ) - C_D/m`. Hence `def^2 >= w (1 - f(δ) - C_D/m)`. Since `d_Ham` is
bi-invariant, `d_Ham(φ(g)φ(h), φ(gh)) = d_Ham(δ, 1) = 1 - f(δ)`, and the displayed bound of Theorem A follows. When
`lim_ω w_k = w > 0`, the right side tends to `0`.

**Sofic trace.** Asymptotic multiplicativity in `d_Ham` means that `g -> [φ_k(g)]` is a homomorphism from `G` into the
metric ultraproduct `Π_ω (Sym(m_k), d_Ham)`. Its kernel is `N_s = {g : lim_ω d_Ham(φ_k(g), 1) = 0} = {τ_s = 1}`. So
`G/N_s` embeds in a metric ultraproduct of symmetric groups, and is therefore sofic (Elek-Szabo 2005; Pestov, Bull.
Symbolic Logic 14 (2008), recalled, not quoted).

**Commutator.** Let `z = aba^{-1}b^{-1}`, so `zba = ab`. Every `π_k(g)` is unitary. Three defect steps give
```text
π(z)π(b)π(a)  ≈  π(zb)π(a)  ≈  π(zba) = π(ab)  ≈  π(a)π(b),
```
each with error `<= def_F`. So `||π(z) - π(a)π(b)π(a)^*π(b)^*||_2 <= 3 def_F`. The scalars `c` cancel in the group
commutator, so `π(a)π(b)π(a)^*π(b)^* = ρ(κ)` with `κ = [φ(a), φ(b)]`, an even permutation. Then
```text
||ρ(κ) - 1||_2^2  =  Σ_i p_i (2 - 2 Re t_i(κ)).
```
- A one-dimensional constituent of `Sym(m)` is trivial or the sign, and `κ` is even, so its term is `0`.
- A constituent of dimension `> 1` has `Re t_i(κ) >= f(κ)^j - C_D/m` by (4), using `sgn κ = 1` for the conjugate
  constituents. Bernoulli's inequality gives `f^j >= 1 - j(1-f) >= 1 - D(1-f)`.

Hence `||ρ(κ) - 1||_2^2 <= 2w (D(1 - f(κ)) + C_D/m)`, which gives the commutator bound (with `3` in place of `4`).
The same three steps in `d_Ham`, which is bi-invariant, give `d_Ham(φ(z), κ) <= 3 max_F d_Ham(φ(g)φ(h), φ(gh)) -> 0`
when `w > 0`.

**Consequences.** Suppose `lim_ω ||π_k(z) - 1||_2 > 0`.
- If `w = 0`, then `||ρ(κ) - 1||_2^2 <= 4 w_k -> 0` (only constituents of dimension `> 1` contribute), so
  `π(z) -> 1`, a contradiction.
- If `w > 0` and `τ_s(z) = 1`, then `f(φ(z)) -> 1`, so `f(κ) -> 1`, and the commutator bound gives `π(z) -> 1`, a
  contradiction.

So `w > 0` and `τ_s(z) < 1`.

## Step 7. Corollary B

Let `V = F_2^{(N)}` with basis `e_0, e_1, ...`. Let `S e_i = e_{i+1}`, `T e_0 = 0`, `T e_i = e_{i-1}`. Then `TS = 1`,
and `Q = 1 - ST` is the projection onto `e_0`.

**Faithfulness.** The words `S^a T^b` span `J` (delete every `TS`). The operator `S^a T^b` kills `e_0, ..., e_{b-1}`
and sends `e_b` to `e_a`. If `Σ c_{ab} S^a T^b = 0` is a finite relation, let `b_0` be the least `b` that occurs.
Evaluating at `e_{b_0}` gives `Σ_a c_{a b_0} e_a = 0`, so every `c_{a b_0} = 0`. Induction shows the relation is
trivial. So `J -> End(V)` is injective, and `E_n ⊂ GL_n(J) ⊂ GL(V^n)` faithfully. The matrix units
`E_{ab} = S^a Q T^b` (sending `e_b -> e_a`) lie in `J` and span the ideal `I = (Q)` of finite-rank operators.

**The finitary kernel is simple and inside `E_n`.** Let `L = GL_fin(V^n, F_2)` be the group of invertible operators
of the form `1 + (finite rank)`, with respect to the basis `{e_a^{(i)}}`.
- *`L ⊂ E_n`.* For basis vectors `p = e_a^{(i)}` and `q = e_b^{(j)}`:
  - if `i ≠ j`, the transvection `1 + E_{pq}` is `x_ij(E_{ab}) ∈ E_n`;
  - if `i = j` and `p ≠ q`, pick `k ≠ i` and `r = e_0^{(k)}`; then `1 + E_{pq} = [1 + E_{pr}, 1 + E_{rq}]`.

  Every element of `L` lies in some `SL_N(F_2) = GL_N(F_2)` on a finite coordinate subspace, and that group is
  generated by these transvections.
- *`L` is normal in `E_n`.* `L = E_n ∩ (1 + M_n(I))`. It is the kernel of `E_n -> GL_n(J/I)`, because an inverse of
  `1 + X` with `X ∈ M_n(I)` is again `≡ 1` modulo the ideal.
- *`L` is simple.* It is the directed union of the simple groups `SL_N(F_2)`, `N >= 3`.
- *`z_Q ∈ L`.* We have `z_Q = x_13(Q) ∈ L \ {1}`.

**Trivial centralizer.** Let `g ∈ GL(V^n)` commute with every `E_{pq}`, `p ≠ q`. Applying `E_{pq} g = g E_{pq}` to a
basis vector `e_r` gives `g_{qr} e_p = δ_{qr} g e_p`. Taking `r ≠ q` gives `g_{qr} = 0`, so `g` is diagonal. Taking
`r = q` gives `g_{pp} = g_{qq}`. So `g` is a nonzero scalar over `F_2`, that is `g = 1`. Hence `C_{E_n}(L) = 1`.

**The head forces soficity.** Take an asymptotic symmetric model of bounded depth `D` with
`lim_ω ||π_k(z_Q) - 1||_2 > 0`. By Step 6, `w > 0` and `z_Q ∉ N_s`.
- `N_s ∩ L` is normal in the simple group `L` and misses `z_Q`, so `N_s ∩ L = 1`.
- `N_s` and `L` are both normal in `E_n`, so `[N_s, L] ⊂ N_s ∩ L = 1`, and `N_s ⊂ C_{E_n}(L) = 1`.
- So `E_n = E_n / N_s` is sofic.

**Converse.** Let `E_n` be sofic, with a separating sofic approximation `φ_k`: asymptotically multiplicative in `d_Ham`,
with `d_Ham(φ_k(g), 1) -> 1` for `g ≠ 1`. Let `ρ` be the standard representation `S^{(m-1,1)}` (`D = 1`), whose
character ratio is `(F - 1)/(m - 1)`. For permutations `α, β` with `d = d_Ham(α, β)`,
```text
||ρ(α) - ρ(β)||_2^2  =  2 - 2 (m(1-d) - 1)/(m-1)  =  2 m d / (m-1).
```
So `π_k = ρ ∘ φ_k` has `def -> 0`, and `||π_k(z_Q) - 1||_2^2 -> 2`.

**Pullback from `Δ`.** The unital ring map `J -> R`, `S -> s_2`, `T -> t_2`, respects `TS = 1`, since `t_2 s_2 = 1`,
and sends `Q` to `1 - s_2 t_2 = s_1 t_1`. This is the complementary Toeplitz algebra of the target's calibration
entry. Let `ψ` be the composite
```text
EL_5(J)  ≅  St_5(J)  ->  St_20(J)  ->  St_20(R).
```
- The first map is (JSI3) of `binary-jacobson-steinberg-cover-is-elementary`. Its inverse sends `x_13(Q)` to the
  Steinberg generator `x_13(Q)`.
- The second map is rank stabilization, `x_ij(a) -> x_ij(a)`.
- The third map is functoriality.

Then `ψ(z_Q) = x_13(s_1 t_1) = z`. If `π_k` is an asymptotic symmetric model of `Δ` of depth `<= D` that sees `z`,
then `π_k ∘ ψ` (with `φ_k ∘ ψ` and `c_k ∘ ψ`) is one of `EL_5(J)` that sees `z_Q`. So `EL_5(J)` is sofic, and so is its
upper-left subgroup `EL_3(J)`.

## Step 8. Uniformity in depth

Put `C'_D = max_{j <= D} C_j`, which is nondecreasing and finite. Let
```text
h(m) = max{ D >= 0 : 4D <= m,  C'_D <= m^{1/2} }.
```
Then `h` is unbounded: every `D` is admitted once `m >= max(4D, C'_D^2)`. If `D_k <= h(m_k)`, then Lemma CA applies to
every constituent, with error `<= m_k^{-1/2}`. Steps 1-6 then give:
- the Hamming bound `d_Ham <= def^2/w_k + m_k^{-1/2}`;
- that `(φ_k)` is a sofic approximation and `G/N_s` is sofic;
- the commutator bound with `D_k` in place of `D`.

**Scope limit.** With `D_k -> ∞`, the commutator bound gives `π(z) -> 1` only when `D_k · d_Ham(κ_k, 1) -> 0`. So the
head conclusion of Corollary B needs bounded depth, or that rate. A model of depth `D_k -> ∞` with `D_k <= h(m_k)`
can see the head in only two ways:
- through `τ_s(z) < 1`, in which case the argument of Step 7 makes `E_n` sofic;
- with `τ_s(z) = 1` but `d_Ham(φ_k(z), 1) >= c/D_k`. This is the surviving growing-depth case.
