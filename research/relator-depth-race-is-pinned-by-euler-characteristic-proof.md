---
rg: 2
id: relator-depth-race-is-pinned-by-euler-characteristic-proof
kind: route
title: The five-term sequence of M_L -> N_L -> N plus multiplicativity of chi give the excess identity; integrality of chi gives the dichotomy; Swan on finite quotients plus b_1(N) = 0 and Maschke give the regular-representation form; Lück approximation on the truncated presentation complex gives the scale-by-scale asymptotics
target: relator-depth-race-is-pinned-by-euler-characteristic
requires:
  - rf-weak-bass-defect-is-degree-two-approximation-defect
  - folner-transversals-kill-local-degree-two-homology
  - amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar
---

Notation as in the target. Homology has coefficients in `Q` unless stated otherwise, and
`b_k = dim_Q H_k`.

## 1. The excess identity (item 1)

Fix a finite-index `N <= K` and `L`. The extension `1 → M_L → N_L → N → 1` has the five-term
exact sequence

> `H_2(N_L) → H_2(N) → H_0(N_L; H_1(M_L)) → H_1(N_L) → H_1(N) → 0`.

The image of the first map is `I_L(N)` by definition. Exactness gives

> `dim H_0(N_L; A_L) = (b_2(N) − dim I_L(N)) + b_1(N_L) − b_1(N)`,

so `e_L(N) = b_2(N) − b_1(N) − dim I_L(N) = χ_Q(N) − 1 − dim I_L(N)`. By item 3 of
`rf-weak-bass-defect-is-degree-two-approximation-defect` (finitely generated, cd `<= 2`,
`b_2 < ∞`; no amenability), `χ_Q(N) = [K:N]χ`. This is the identity. The bounds follow from
`0 <= dim I_L(N) <= n|TB_L \ T|`, which is item 1 of `folner-transversals-kill-local-degree-two-homology`
and holds for every group and every transversal. If `L <= ρ_ε(N)`, some `L' >= L` and some
transversal `T` have `|TB_{L'} \ T| <= ε|T| = ε[K:N]`. Since `B_L ⊂ B_{L'}`, the same bound holds
at `L`, which gives the last line of item 1. ∎

## 2. One cover decides, and the dichotomy (item 2)

**(a).** Suppose `ℓ = ℓ^δ(N) <= ρ_ε(N)`. By §1 there is a transversal `T` with
`|TB_ℓ \ T| <= ε[K:N]`. The definition of `ℓ^δ` gives `dim I_ℓ(N) >= b_2(N) − δ[K:N]`, and the
Følner bound gives `dim I_ℓ(N) <= nε[K:N]`. So `b_2(N) <= (δ + nε)[K:N]`. On the other hand,
`b_2(N) = χ[K:N] − 1 + b_1(N) >= χ[K:N] − 1`. Hence `χ[K:N] <= 1 + (δ + nε)[K:N] < [K:N]`, using
`(1 − δ − nε)[K:N] > 1`. Since `χ ∈ Z`, `χ <= 0`.

For the second form, `e_L(N) <= δ[K:N]` and item 1 (with `L <= ρ_ε(N)`) give
`χ[K:N] − 1 − nε[K:N] <= δ[K:N]`, and the same arithmetic gives `χ <= 0`. If `K` is amenable and
residually finite, item 4 of `rf-weak-bass-defect-is-degree-two-approximation-defect` gives
`χ = D(P) >= 0`, so `χ = 0`. ∎

**(b).** First suppose `χ = 0`. Then `b_2(N_i) = b_1(N_i) − 1`, and `b_1(N_i) = o([K:N_i])` by item
4 of `rf-weak-bass-defect-is-degree-two-approximation-defect`. For a fixed `δ > 0`, eventually
`b_2(N_i) <= δ[K:N_i]`, so `L = 0` satisfies `dim I_0(N_i) = 0 >= b_2(N_i) − δ[K:N_i]`, i.e.
`ℓ^δ(N_i) = 0`. Item 1 gives `e_L(N_i) = −1 − dim I_L(N_i) < 0` for every `L`.

Now suppose `χ >= 1` and `ε > 0`. Since `[K:N_i] → ∞` (`K` is infinite and the chain is
residual), `(1 − δ − nε)[K:N_i] > 1` for large `i`. Part (a) then forbids `ℓ^δ(N_i) <= ρ_ε(N_i)`,
because `χ >= 1 > 0`. Weiss's theorem, as used in item 5 of
`folner-transversals-kill-local-degree-two-homology`, gives `ρ_ε(N_i) → ∞` for every `ε > 0`.
The lower bound on `e_L(N_i)` is item 1. ∎

**(c).** The quantity to be bounded is `e_L(N_i)` with `L = ρ_ε(N_i)`. If `e_L(N_i) <= δ[K:N_i]`
for one large `i`, then `χ = 0` by (a). If `χ = 0`, then `e_L(N_i) < 0` for all `L` by (b). For
the last sentence, item 1 gives `e_L(N) = b_2(N) − b_1(N) − dim I_L(N)`. So
`e_L(N) <= δ[K:N]` together with `dim I_L(N) <= nε[K:N]` gives
`b_2(N) <= (δ + nε)[K:N] + b_1(N)`, where `b_1(N_i) = o([K:N_i])`. Conversely,
`b_2(N) <= (δ + nε)[K:N]` with `δ + nε < 1` forces `χ = 0` by the arithmetic of (a), and then
`e_L < 0`. ∎

## 3. The counterexample's finite-quotient modules (item 3)

**b_1 vanishes on every finite-index subgroup.** Let `K` be amenable with `χ >= 1`, and let
`N <= K` have finite index. Then:
- `N` is finitely generated, amenable and torsion-free.
- `χ_Q(N) = [K:N]χ >= 1` by item 3 of the defect node.
- If `K = 1`, item 3 is trivial (`F = 1`, `H_2 = 0`, `χ = 1`), so assume `K` is infinite; then
  so is `N`. If `cd N <= 1`, then `N` is free (Stallings–Swan), nontrivial and amenable, so
  `N ≅ Z` and `χ_Q(N) = 0`, a contradiction. So `cd N = 2`.
- `N` is not solvable. A finitely generated solvable group of cd 2 is elementary amenable, hence
  `BS(1,m)` by Kropholler–Linnell–Lück, and has `χ_Q = 0`.

So `N` is a two-dimensional counterexample in the sense of item 3 of
`amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`. Item 3(c) there, applied to the
trivial normal subgroup of `N`, says `N` has no infinite elementary amenable quotient. If
`b_1(N) > 0`, then `N` maps onto `Z`, a contradiction. So `b_1(N) = 0`, and therefore
`b_2(N) = χ_Q(N) − 1 = χ[K:N] − 1`.

**The module `H_2(N)`.** Now let `N` be normal, with `F = K/N`. Let `P` be the relation module of
the `n`-generator presentation. It is projective because `cd K <= 2`, and it sits in the exact
sequence

> `0 → P → Z[K]^n → Z[K] → Z → 0`.

Apply `Q[F] ⊗_{Z[K]} −`. By Shapiro's lemma, the homology of the resulting complex

> `Q[F] ⊗ P → Q[F]^n → Q[F]`

is `H_*(N; Q)`, and all maps are `Q[F]`-linear, with `F` acting on `H_*(N)` by conjugation. So
`H_2(N)` is the kernel of the first map, `H_1(N) = 0` is the homology at the middle term, and
`H_0(N) = Q` is the cokernel of the last map. This gives an exact sequence of `Q[F]`-modules

> `0 → H_2(N) → Q[F] ⊗ P → Q[F]^n → Q[F] → Q → 0`.

Item 1 of the defect node gives `Q[F] ⊗ P ≅ Q[F]^r` with `r = r(P) < ∞`. Here
`r(P) = b_2(K) + n − b_1(K) = n − 1 + χ`: tensor the resolution with `Q`, and note that
`Q^n → Q` is zero. `Q[F]` is semisimple (Maschke), so every exact sequence of finite-dimensional
`Q[F]`-modules splits. For `0 → A → B → C → D → E → 0` this gives `A ⊕ C ⊕ E ≅ B ⊕ D`. Here that
reads

> `H_2(N) ⊕ Q[F]^n ⊕ Q ≅ Q[F]^{n−1+χ} ⊕ Q[F]`.

Krull–Schmidt cancellation of `Q[F]^n` gives `H_2(N) ⊕ Q ≅ Q[F]^χ`.

**The long-relation coinvariants.** `Γ_L` acts by conjugation on `M_L` and on `N_L`, since both
are normal in `Γ_L`. So the five-term sequence of §1 is a sequence of `Q[Γ_L]`-modules. Inner
automorphisms by `N_L` act trivially on `H_*(N_L)`, on `H_*(N)` and on `H_0(N_L; A_L)`, so this is
a sequence of `Q[Γ_L/N_L] = Q[F]`-modules. With `H_1(N) = 0` it reads

> `0 → H_2(N)/I_L(N) → H_0(N_L; A_L) → H_1(N_L) → 0`.

Maschke gives `H_0(N_L; A_L) ≅ H_2(N)/I_L(N) ⊕ H_1(N_L)`, and `H_2(N) ≅ I_L(N) ⊕ H_2(N)/I_L(N)`.
So

> `H_0(N_L; A_L) ⊕ I_L(N) ⊕ Q ≅ H_2(N) ⊕ Q ⊕ H_1(N_L) ≅ Q[F]^χ ⊕ H_1(N_L)`.

The summand `I_L(N) ⊕ Q` has dimension `<= n|TB_L \ T| + 1` by the Følner bound.

**Twisted coefficients.** Let `V` be a finite-dimensional `Q[K]`-module on which `N` acts
trivially, with `N` normal of finite index. Since `F` is finite and the coefficients have
characteristic 0, the Lyndon–Hochschild–Serre spectral sequence collapses, and
`H_p(K; V) = (H_p(N) ⊗ V)_F`. So `H_1(K; V) = 0`, and

> `dim H_2(K; V) = dim (Q[F]^χ ⊗ V)_F − dim (Q ⊗ V)_F = χ dim V − dim V_K`,

using `(Q[F] ⊗ V)_F ≅ V`. ∎

## 4. Scale-by-scale asymptotics (item 4)

Let `K` be infinite, residually finite and amenable, and fix `L`. Let `Z_L = M_L \ Ỹ_L`, the
covering of `Y_L` with deck group `K`. This is a free `K`-CW complex with finitely many cells:
one 0-cell, `n` 1-cells and `c = |R_{≤L}|` 2-cells per orbit. `π_1(Z_L) = M_L`, so
`H_1(Z_L; Q) = A_L` as `Q[K]`-modules.

**`b_1(N_{i,L})`.** The quotient `N_i \ Z_L` is the covering of `Y_L` with fundamental group
`N_{i,L}`, and `H_1` of a CW complex is `H_1` of its fundamental group. So
`b_1(N_{i,L}) = b_1(N_i \ Z_L)`. Lück's approximation theorem, for the finite free `K`-CW complex
`Z_L` along the residual chain `(N_i)`, gives

> `b_1(N_i \ Z_L)/[K:N_i] → b_1^{(2)}(Z_L; N(K))`.

`K` is amenable, so `N(K)` is dimension-flat over `C[K]` (Lück, Thm 6.37). Hence
`b_1^{(2)}(Z_L) = dim_{N(K)} (N(K) ⊗_{Q[K]} H_1(Z_L; Q)) = dim_U (U ⊗ A_L) = β_1(L)`. The middle
equality uses that `U` is the Ore localization of `N(K)`, which is flat over it and preserves
dimension.

**`β_1(L)` decreases to 0.** Let `P_L ≤ P` be the image of the `c` relator cells, i.e. the
submodule of the cycle module `P = Z_1(Cay(K,S); Q)` generated by the relators of length `<= L`.
Since `H_1(Z_L) = Z_1/B_1` and `Z_1(Z_L) = P` (the 1-skeleton of `Z_L` is the Cayley graph), we
have `A_L = P/P_L`. `U ⊗ −` is right exact, so `U ⊗ P_L → U ⊗ P → U ⊗ A_L → 0` is exact, and
additivity gives

> `β_1(L) = dim_U(U ⊗ P) − dim_U im(U ⊗ P_L → U ⊗ P)`.

The images increase with `L`, and their union is `U ⊗ P`, since `P = ⋃ P_L` and `⊗` commutes
with directed colimits. By cofinality, their dimensions tend to `dim_U(U ⊗ P) = d(P)`. This is
`n − 1`, which is finite: `r(P) = n − 1 + χ` (§3) and `D(P) = r(P) − d(P) = χ` (item 4 of the
defect node). So `β_1(L)` is non-increasing, and `β_1(L) → 0`.

**The coinvariants.** §1 gives
`dim H_0(N_{i,L}; A_L) = e_L(N_i) + b_1(N_{i,L}) = χ[K:N_i] − 1 − dim I_L(N_i) + b_1(N_{i,L})`.
Item 3 of `folner-transversals-kill-local-degree-two-homology` gives
`dim I_L(N_i) = o([K:N_i])` for fixed `L`. Together with the first paragraph, this gives
`dim H_0(N_{i,L}; A_L) = (χ + β_1(L))[K:N_i] + o([K:N_i])`. ∎

## 5. Calibrations (item 5)

**(a).** A finitely generated elementary amenable group of cd 2 is `BS(1,m)`, `m ≠ 0`
(Kropholler–Linnell–Lück). This includes `Z² = BS(1,1)` and the Klein bottle group `BS(1,−1)`,
and it covers every finitely generated solvable group of cd 2. Each has a one-relator aspherical
presentation. So, with `L_0` the length of that relator, `I_{L_0}(N) = H_2(N)` for every `N`
(for `L >= L_0`, `Γ_L = K` and `M_L = 1`), and `ℓ^0(N) <= L_0`. `χ = 0` by the Euler
characteristic of the aspherical presentation complex, so item 2(b) applies. The final sentence
of item 5(a) is §3.

**(b).** `Z²` with `N = (mZ)²` and `F = K/N ≅ (Z/m)²`. For `L < 4` there are no relators,
`Γ_L = F_2` and `M_L = [F_2, F_2]`. `A_L = H_1(M_L; Q) = Q ⊗ P ≅ Q[K]`, because the presentation
is aspherical with one relator. So `H_0(N_L; A_L) = Q[F]` has dimension `m²`, and `N_L` is free
of rank `m² + 1` (Schreier). Hence `e_L = m² − (m² + 1) = −1 = χ[K:N] − 1 − 0`. For `L >= 4`,
`Γ_L = K`, `A_L = 0` and `N_L = N ≅ Z²`, so `e_L = −2 = −1 − dim I_L(N)` with `I_L(N) = H_2(N)`
of dimension 1. `β_1(L) = 1` for `L < 4` and `0` for `L >= 4`, and `b_1(N_L)/m² → 1 = β_1(L)`,
as item 4 says.

**(c).** For the lattice `Γ` of `pro-p-route-cannot-see-amenability-in-cd-two`, item 6 of
`folner-transversals-kill-local-degree-two-homology` gives `I_3(N) = H_2(N)` of dimension
`V[Γ:N] − 1`. `I_L(N) = 0` for `L < 3` because there are no relators, so item 1 gives the stated
values of `e_L`. Property (T) passes to finite-index subgroups and forces finite abelianization, so
`b_1(N) = 0`. The derivation of `H_2(N) ⊕ Q ≅ Q[F]^χ` in §3 used only that fact, projectivity of
`P`, `r(P) < ∞` and item 1 of the defect node (which holds for every group). So it applies to
`Γ` with `χ = V`. ∎
