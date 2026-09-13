# Cyclic centralizers for linear north--south annulus units of the binary Leavitt algebra

Lane `ex2-q34-commuting-units`, 2026-09-13. Complete proofs, unreviewed. This extends the coefficient argument of
`research/artifacts/leavitt-north-south-centralizer-2026-09-12.md` (lane `ex-q34-leavitt-hs`) from the Thompson
unit `c` to a class of units that are linear on a bounded middle region.

## 0. Definitions and statement

`R = L_(F_2)(1,2)` and `Q = R^x`. `R` acts faithfully on `M = C(X, F_2)`, the locally constant functions on
`X = {0,1}^N`, by `(s_α t_β f)(x) = 1_[α](x) f(β σ^|α| x)`. So `(t_ζ f)(x) = f(ζ x)`. For a clopen set `D`, put
`e_D = 1_D` and `M_D = e_D M`. `μ` is the Bernoulli `(1/2, 1/2)` measure.

**Definition.** A unit `u ∈ Q` is a *north--south annulus unit* if it has the following data:
- words `ζ, γ, ξ, δ`, with `γ, δ` nonempty and `[ζ] ∩ [ξ] = ∅`;
- an integer `m >= 1`, and clopen sets `D_(-m+1), ..., D_(-1)`.

Put `p = ζγ^∞` and `q = ξδ^∞`. Put `D_k = [ζγ^k] \ [ζγ^(k+1)]` for `k >= 0`, and
`D_(-m-j) = [ξδ^j] \ [ξδ^(j+1)]` for `j >= 0`. The data must satisfy:
- (N1) `u s_ζ = s_(ζγ)` and `t_(ζγ) u = t_ζ`: clean attraction to `p`;
- (N2) `u^(-1) s_ξ = s_(ξδ)` and `t_(ξδ) u^(-1) = t_ξ`: clean repulsion from `q`;
- (N3) `X = {p, q} ⊔ ⊔_(k ∈ Z) D_k`;
- (N4) `u e_(D_k) u^(-1) = e_(D_(k+1))` for `-m <= k <= -1`.

**Consequence of N1 and N2.** `u e_([ζ]) u^(-1) = s_(ζγ) t_ζ u^(-1) = s_(ζγ) t_(ζγ)`. Likewise
`u e_([ξδ]) u^(-1) = e_([ξ])`. So `u e_(D_k) u^(-1) = e_(D_(k+1))` for every `k`, and `u M_(D_k) = M_(D_(k+1))`.
Iterating N1 and N2 gives `u^j s_ζ = s_(ζγ^j)`, `t_ζ u^(-j) = t_(ζγ^j)`, and `t_ξ u^j = t_(ξδ^j)` for `j >= 0`.

**Examples.**
- The Thompson unit `c = s_00 t_0 + s_01 t_10 + s_1 t_11`, with `ζ = γ = 0`, `ξ = δ = 1`, `m = 1`,
  `D_0 = [01]` and `D_(-1) = [10]`.
- *Linear twists.* For any unit `w` of the corner `e_([10]) R e_([10])`, put `u = c (w + 1 - e_([10]))`.
  - For instance `w = e_([10]) + n` with `n ∈ s_10 R t_10` nilpotent.
  - The second factor commutes with every `e_(D_k)`, so N4 holds.
  - It is the identity on `[0]` and `[11]`, so N1 and N2 hold with the same data.
  - `u` is not a Thompson unit when `w != e_([10])`.
- Products `c u_(-1)` with a unit `u_(-1)` supported on the annulus `D_(-1)`, and conjugates of all these by `Q`.

**Theorem.** Let `u` be a north--south annulus unit and `a != 0`. Then:
1. `C_R(u^a) = F_2[u, u^(-1)]`, a Laurent polynomial ring in `u`;
2. `C_Q(u^a) = <u>`.

Both statements pass to every `Q`-conjugate of `u`.

## 1. Two tools (as in the Thompson case)

**Lemma 1 (support measure).** For `x ∈ R` of depth `N` with `T` terms, `μ(supp(x f)) <= T 2^N μ(supp f)`.
*Proof.* Each term maps `supp f ∩ [β]` by a prefix replacement, which scales measure by at most `2^N`. ∎

**Lemma 2 (killing the flow kills everything).** Put `M_flow = ⊕_(k ∈ Z) M_(D_k)`, the functions vanishing near
`p` and `q`. If `x ∈ R` kills `M_flow`, then `x = 0`.
*Proof.* Let `ξ'` be aperiodic, and `N_(ξ')` the Chen module on its tail class, with
`s_α t_β e_(βw) = e_(αw)`. Every `η` in the class is aperiodic, so it differs from the periodic points `p` and
`q`. It has a clopen neighbourhood `A` avoiding both, and `e_A e_η = e_η`. Also `x e_A = 0`, because
`x e_A M ⊆ x M_flow = 0` and `M` is faithful. So `x` kills the nonzero module `N_(ξ')`, and `x = 0` by
simplicity of `R` (`leavitt-algebras-l-k-1-n-are-simple`). ∎

## 2. Step 1: `g M_flow ⊆ M_flow`

Let `g ∈ C_R(u^a)`. We may take `a > 0`. Let `f ∈ M_flow`, so `f ∈ ⊕_(|k| <= K) M_(D_k)`, and put `h = g f`.
- **Near `p`.** Suppose `h` does not vanish near `p`. Then `h = 1` on some `[ζγ^J]`.
  - For `am >= J`, `t_ζ u^(-am) h = t_(ζγ^(am)) h = 1`, so `u^(-am) h = 1` on `[ζ]`.
  - On the other hand `u^(-am) h = g u^(-am) f`, and `u^(-am) f ∈ ⊕_(|k| <= K) M_(D_(k-am))`. Its support
    measure `Σ_k μ(D_(k-am))` tends to `0`.
  - By Lemma 1, `μ(supp(g u^(-am) f)) -> 0`, which contradicts `μ([ζ]) > 0`.
- **Near `q`.** The same argument with `t_ξ u^(am) = t_(ξδ^(am))` and the annuli `D_(k+am)`. ∎

## 3. Step 2: reading coefficients near `p`

Let `N` be the depth of `g`. Fix `f_0 ∈ M_(D_0)`. Then `f_0 = s_ζ F` for a function `F` supported off `[γ]`, and
for `n >= 0`, `u^n f_0 = s_(ζγ^n) F`, supported in `D_n`.

**Aligned terms.** Call a term `(α, β)` of `g` *aligned* if `β` is a prefix of `p` and
`α σ^|β|(p) = p` as infinite words. For aligned terms, `|α| - |β| = d|γ|` with `d ∈ Z`. Put
`ε_d = #{ aligned terms with shift d } mod 2` and `p_g(t) = Σ_d ε_d t^d ∈ F_2[t^(±1)]`.

**Claim.** For all large `n`, `g u^n f_0 = Σ_d ε_d u^(n+d) f_0`.

*Proof.* A term `(α, β)` contributes at `y = αρ` only if `βρ ∈ supp(u^n f_0) ⊆ [ζγ^n]`. For
`n|γ| > N + |ζ|`, this forces `β` to be a prefix of `p` and `y = α σ^|β|(ζγ^n) x`, where `x` is the fibre point.
- *Aligned terms.* Then `y = ζγ^(n+d) x`, and the contribution is exactly `u^(n+d) f_0`.
- *Non-aligned terms.* Then `α σ^|β|(p) != p`. Both words are eventually `γ`-periodic, so they differ within
  the first `N + |ζ| + 2|γ|` letters. So `y ∉ [ζγ^c]` for a fixed `c`.
- *Commutation.* Step 1 gives `g f_0 ∈ ⊕_(j ∈ S) M_(D_j)` for a finite set `S`. For large `n`, commutation puts
  `g u^n f_0 = u^n g f_0` in `⊕_(j ∈ S) M_(D_(n+j)) ⊆ M_([ζγ^c])`.
- *Conclusion.* The non-aligned part is this vector minus the aligned part, so it lies in `M_([ζγ^c])`. It is
  also supported off `[ζγ^c]`, so it is `0`. ∎

For every `n >= 0` and large `k`, the claim at `n + ak` gives
`u^(ak) g u^n f_0 = g u^(ak+n) f_0 = u^(ak) p_g(u) u^n f_0`. Applying `u^(-ak)`,

```text
g = p_g(u)   on   ⊕_(n >= 0) M_(D_n) = ⊕_(n >= 0) u^n M_(D_0) .
```

For `k < 0`, choose `r >= 0` with `k + ar >= 0`. For `f ∈ M_(D_k)`,
`g f = u^(-ar) g u^(ar) f = u^(-ar) p_g(u) u^(ar) f = p_g(u) f`. So `g = p_g(u)` on `M_flow`.

## 4. Step 3: conclusion

`g - p_g(u)` kills `M_flow`, so `g = p_g(u)` by Lemma 2, and `C_R(u^a) ⊆ F_2[u^(±1)]`. The reverse inclusion is
clear. `M_flow = ⊕_k u^k M_(D_0)` is a free `F_2[t^(±1)]`-module with `t` acting as `u`, so `p(u) = 0` forces
`p = 0`, and `F_2[u^(±1)]` is a Laurent polynomial ring. Its units are the monomials, which gives item 2. ∎

## 5. Consequences

**Heisenberg subgroups.** No element of infinite order of a subgroup `H ≅ H_3(Z)` of `Q` is conjugate to a
north--south annulus unit.
- *Central elements* `c^j`. By Proposition 5 of `research/artifacts/leavitt-unit-centralizer-rank-2026-09-13.md`,
  `C_R(c^j)` has infinite rank over `F_2[c^j]`, while the theorem gives rank `1`.
- *Non-central `x ∈ H`.* The commutator `[x, y]` with some `y ∈ H` is central of infinite order, and lies in
  `C_Q(x) = <x>`, so `[x,y] = x^i`. Then `x^i`, a nonzero power of `x`, is central, which is false in `H_3(Z)`
  for a non-central `x`.

**Baumslag--Solitar bases.** If `t x t^(-1) = x^k` with `|k| >= 2`, then `x` is not conjugate to an annulus unit.
Proposition 6 of the same artifact gives infinite rank.

**Question 5.7.** Let `f : L ⊗ L -> L` be a unital embedding. For no unit `g ∈ L` of infinite order is
`f(g ⊗ 1)` conjugate to an annulus unit.
- If it were, then `f(1 ⊗ c) ∈ C_R(f(g ⊗ 1)) = F_2[f(g ⊗ 1)^(±1)]`.
- By injectivity, `1 ⊗ c ∈ F_2[g^(±1)] ⊗ 1`, which is false.
- The same holds for `f(1 ⊗ g)`.

## 6. Scope: why persistent leading terms are not enough

**The germ map at a clean attracting germ.** Suppose only N1 holds. For `g ∈ C_R(u)`,
- `t_(ζγ^k) g s_(ζγ^k) = t_ζ g s_ζ =: κ(g)` for every `k`, because `s_(ζγ^k) = u^k s_ζ` and
  `t_(ζγ^k) = t_ζ u^(-k)`;
- `κ(g)` is a polynomial `Σ_d ε_d x_d`, with `x_d = s_γ^d` for `d >= 0` and `x_d = t_γ^|d|` for `d < 0`;
- `κ(u g) = κ(g) s_γ` and `κ(u^(-1) g) = t_γ κ(g)`.

So `g -> Σ ε_d t^d` is an `F_2[u^(±1)]`-linear map `C_R(u) -> F_2[t^(±1)]`. N1 alone bounds the part of `C_R(u)`
seen at `p` by rank `1`. It does not control elements with zero germ at `p`, such as blocks of `phi(c)` living
near the second attractor.
- **Where the extension to persistent leading terms dies.** A persistent free-group leading term
  `s_(νγ) 1_E t_ν` (`leavitt-free-group-leading-term-forces-linear-depth`) supplies an attracting ray at
  `νγ^∞` for the leading part only.
- Lower terms of `u` exit that ray and return to it, so no identity like N1 holds for any power of `u`.
- The compressions `t_(νγ^k) (·) s_(νγ^k)` are then not multiplicative. The middle region, where N4 is used,
  has no analogue.
- No argument covering these units is known.
