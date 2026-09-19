---
rg: 2
id: leavitt-cone-cover-hamming-head-bound-proof
kind: route
title: Shadow a Hamming counterexample to the cone bound through the set section, spread the head to every element by simplicity, amplify by tensor powers to a sofic approximation of Delta, and contradict nonsoficity of the unit group
target: leavitt-cone-cover-hamming-head-bound-holds
requires:
  - openai-leavitt-unit-nonsofic
  - leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding
  - leavitt-cuntz-cone-halves-have-rf-amalgam-cover
  - binary-leavitt-elementary-group-is-simple
  - leavitt-steinberg-map-iso-from-rank-three
---

Notation as in the target. For permutations `u, v, w` of a finite set `X`, with
`Mov(u) = {x : ux != x}` and `d_H(u, v) = d(v^(-1) u)`:

```text
Mov(uv) ⊆ Mov(u) ∪ Mov(v),  so  d(uv) <= d(u) + d(v);
d(w u w^(-1)) = d(u) = d(u^(-1));   d_H(uv, w) = d(w^(-1) u v).                               (H)
```

A *Hamming asymptotic homomorphism* of a group `G` is a sequence of maps `σ_n : G -> Sym(X_n)` with
`d_H(σ_n(gh), σ_n(g)σ_n(h)) -> 0` for all `g, h`. `G` is *sofic* (standard definition, Weiss; Elek--Szabó) if for
every finite `F ⊆ G` and `η > 0` there are a finite set `X` and a map `τ : G -> Sym(X)` with
`d_H(τ(gh), τ(g)τ(h)) < η` for `g, h in F` and `d(τ(g)) > 1 - η` for `g in F \ {1}`. Restricting `τ` shows that
subgroups of sofic groups are sofic.

**Inputs.**
- `openai-leavitt-unit-nonsofic`, verbatim: "**Theorem 1.1.** The unit group `L_(F_2)(1,2)^x` is not sofic."
- `leavitt-steinberg-map-iso-from-rank-three` and `binary-leavitt-elementary-group-is-simple`, as used in
  `leavitt-st20-cone-bound-half-rounding-proof` (Inputs): `Delta = St_20(R) = EL_20(R) = GL_20(R)` is simple,
  nontrivial and non-abelian.
- `leavitt-cuntz-cone-halves-have-rf-amalgam-cover`, items 1--3: the halves, `Delta_0 ∋ z`, `Gamma`, `p`,
  `K = <<k_1, ..., k_r>>`.
- `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`, via its route: the set section `s`,
  item 2 (failure of `(QC)` makes `Delta` hyperlinear), and "Nonhyperlinear ⇒ (HR)".

## Step 0: Delta is not sofic

`u -> diag(u, 1, ..., 1)` is an injective homomorphism `R^x -> GL_20(R) = Delta`. By Theorem 1.1 `R^x` is not
sofic. Subgroups of sofic groups are sofic, so `Delta` is not sofic. □

## Step 1: shadowing

Fix the set section `s : Delta -> Gamma` of `leavitt-st20-cone-bound-half-rounding-proof`, part (b): `p s = id`,
`s(1) = 1`, `s(z) = z`. For `g, h in Delta`, `c(g,h) = s(g)s(h)s(gh)^(-1) in K` is a product of `L(g,h)`
conjugates of the `k_i^(+-1)`.

**Lemma 1.** Let `ρ_n` be actions of `Gamma` on finite sets `X_n` with `max_i d(ρ_n(k_i)) -> 0`, and put
`σ_n = ρ_n ∘ s`. Then `σ_n` is a Hamming asymptotic homomorphism of `Delta`, `σ_n(1) = 1`, and `σ_n(z) = ρ_n(z)`.

*Proof.* By (H),
`d_H(σ_n(g)σ_n(h), σ_n(gh)) = d(ρ_n(s(gh))^(-1) ρ_n(s(g)s(h))) = d(ρ_n(s(gh)^(-1) c(g,h) s(gh)))
= d(ρ_n(c(g,h))) <= L(g,h) max_i d(ρ_n(k_i)) -> 0`. The rest is `s(1) = 1`, `s(z) = z`. □

For such `σ_n` and fixed `a_1, ..., a_r in Delta`, induction on `r` with (H) gives

```text
d_H(σ_n(a_1 ... a_r), σ_n(a_1) ... σ_n(a_r)) -> 0,   d_H(σ_n(a^(-1)), σ_n(a)^(-1)) = d(σ_n(a)σ_n(a^(-1))) -> 0,   (W)
```

the second because `d(σ_n(a)σ_n(a^(-1))) <= d_H(σ_n(a)σ_n(a^(-1)), σ_n(1)) + d(σ_n(1))` and `σ_n(1) = 1`.
For a general Hamming asymptotic homomorphism, `d(σ_n(1)) = d_H(σ_n(1)σ_n(1), σ_n(1)) -> 0`, so (W) still
holds.

## Step 2: a head-moving Hamming asymptotic homomorphism makes Delta sofic

**Lemma 2.** Let `σ_n : Delta -> Sym(X_n)` be a Hamming asymptotic homomorphism, `g_0 in Delta`, and `ε > 0`
with `d(σ_n(g_0)) >= ε` for all `n` in an infinite set `N_0`. Then `Delta` is sofic.

*Proof.* Pass to `N_0`. Since `d(σ_n(1)) -> 0`, `g_0 != 1`.
1. **Spread the mark.** Let `g in Delta \ {1}`. Since `Delta` is simple, the normal closure of `g` is `Delta`,
   so `g_0 = ∏_(j=1)^(L) w_j g^(e_j) w_j^(-1)` for some `L = L_g >= 1`, `w_j in Delta`, `e_j = ±1`. By (W) and (H),
   `d(σ_n(g_0)) <= Σ_j d(σ_n(w_j) σ_n(g)^(e_j) σ_n(w_j)^(-1)) + o(1) = L d(σ_n(g)) + o(1)`.
   Hence there is `n(g)` with `d(σ_n(g)) >= ε / (2 L_g)` for `n >= n(g)` in `N_0`.
2. **Tensor powers.** For a permutation `u` of `X` let `u^(⊗k)` act coordinatewise on `X^k`. Then
   `(uv)^(⊗k) = u^(⊗k) v^(⊗k)`, `1 - d(u^(⊗k)) = (1 - d(u))^k` (a tuple is fixed iff every coordinate is), and
   `d_H(u^(⊗k) v^(⊗k), w^(⊗k)) <= k d_H(uv, w)` (union bound over coordinates).
3. **Diagonalize.** Let `F_1 ⊆ F_2 ⊆ ...` be finite sets exhausting the countable group `Delta`. For each `m`
   choose `k_m` with `(1 - ε/(2 L_g))^(k_m) < 1/m` for all `g in F_m \ {1}`. Then choose `n_m in N_0` with
   `n_m >= n(g)` for `g in F_m \ {1}` and `d_H(σ_(n_m)(gh), σ_(n_m)(g)σ_(n_m)(h)) < 1/(m k_m)` for `g, h in F_m`.
   Put `τ_m = σ_(n_m)^(⊗ k_m)`. By step 2, on `F_m` its defects are `< 1/m`, and `d(τ_m(g)) > 1 - 1/m` for
   `g != 1`. Given finite `F` and `η > 0`, take `m` with `F ⊆ F_m` and `1/m < η`. So `Delta` is sofic. □

## Step 3: items 1 and 3 for permutations

*Item 1.* Suppose `(QC_H)` fails. Then there are `ε > 0` and actions `ρ_n` of `Gamma` on finite sets with
`max_i d(ρ_n(k_i)) -> 0` and `d(ρ_n(z)) > ε`. By Lemma 1, `σ_n = ρ_n ∘ s` is a Hamming asymptotic
homomorphism with `d(σ_n(z)) > ε`. By Lemma 2 with `g_0 = z`, `Delta` is sofic, contradicting Step 0. □

*Item 3, permutations.* If some Hamming asymptotic homomorphism had `d(σ_n(g_0))` not tending to `0`, Lemma 2
would make `Delta` sofic, contradicting Step 0. □

## Step 4: finite-phase monomial representations (items 2 and 3)

Fix `m >= 1`, `ζ = e^(2πi/m)`, and `c_m = min(2, |ζ - 1|^2)` (`c_1 = 2`; `c_m > 0`). An element `M` of
`C_m wr Sym(d)` is `M e_j = ζ^(λ_j) e_(π(j))` with `π in Sym(d)`, `λ_j in Z/m`. Let
`B(M) = {j : π(j) != j or λ_j != 0}` and `β(M) = |B(M)|/d`.

**Lemma 3.** `Φ(M)(a, j) = (a + λ_j, π(j))` defines an injective homomorphism
`Φ : C_m wr Sym(d) -> Sym(Z/m × [d])`, and

```text
||M - 1||_2^2 / 4  <=  d(Φ(M)) = β(M)  <=  ||M - 1||_2^2 / c_m.                                   (M)
```

*Proof.* `M M' e_j = ζ^(λ'_j + λ_(π'(j))) e_(π π'(j))`, and
`Φ(M)Φ(M')(a, j) = (a + λ'_j + λ_(π'(j)), π π'(j))`; injectivity is clear. The point `(a, j)` is moved iff
`j in B(M)`, so `d(Φ(M)) = β(M)`. Finally
`||M - 1||_2^2 = d^(-1) Σ_j ||M e_j - e_j||^2 = d^(-1) (Σ_(π(j) != j) 2 + Σ_(π(j) = j) |ζ^(λ_j) - 1|^2)`: every
term with `j in B(M)` lies in `[c_m, 4]`, and every other term is `0`. □

*Item 2.* Given `m` and `ε`, let `δ_H` be the `δ` of `(QC_H)` for `ε^2/4`, and put `δ = (c_m δ_H)^(1/2)`. If
`ρ : Gamma -> C_m wr Sym(d)` has `max_i ||ρ(k_i) - 1||_2 <= δ`, then `Φ ∘ ρ` is an action of `Gamma` on
`Z/m × [d]` with `d(Φρ(k_i)) <= δ^2/c_m = δ_H` by (M). By `(QC_H)`, `d(Φρ(z)) <= ε^2/4`, and by (M)
`||ρ(z) - 1||_2 <= (4 · ε^2/4)^(1/2) = ε`. □

*Item 3, monomial.* Let `σ_n : Delta -> C_m wr Sym(d_n)` be an HS asymptotic homomorphism. By (M) and
`||A - B||_2 = ||B^(-1)A - 1||_2`, `d_H(Φ(A), Φ(B)) = d(Φ(B^(-1)A)) <= ||A - B||_2^2 / c_m`, so `Φ ∘ σ_n` is a
Hamming asymptotic homomorphism. By the permutation case, `d(Φσ_n(g)) -> 0`, and by (M)
`||σ_n(g) - 1||_2^2 <= 4 d(Φσ_n(g)) -> 0`. □

## Step 5: calibration of the split (item 4)

- If `(QC)` fails, then `Delta` is hyperlinear: item 2 of
  `leavitt-st20-nonhyperlinear-iff-cone-bound-and-half-rounding`.
- If `(HR)` fails, then `Delta` is hyperlinear: its route proves "Nonhyperlinear ⇒ (HR)" (part (b)).
- Either way `R^x`, a subgroup of `Delta` by Step 0, is hyperlinear, since hyperlinearity passes to
  subgroups (restrict the asymptotic representations). By Theorem 1.1 it is nonsofic. So it is a hyperlinear
  nonsofic group, which answers `binary-leavitt-unit-group-hyperlinear` and `hyperlinear-nonsofic-group`.
- If both hold, `Delta` is non-hyperlinear by item 1 of the split, which answers `non-hyperlinear-group`. □

## Why the class dies, and what survives

By items 1--2, a refutation of `(QC)` can use no family of permutation or bounded-phase monomial
representations. The same holds for genuine `ρ_n` that are pointwise HS-close to maps `ρ'_n` into
`C_m wr Sym(d_n)` for one fixed `m`, i.e. `||ρ_n(x) - ρ'_n(x)||_2 -> 0` for every `x in Gamma`. Indeed
`σ'_n = ρ'_n ∘ s` then has defect
`||σ'_n(g)σ'_n(h) - σ'_n(gh)||_2 <= o(1) + ||ρ_n(c(g,h)) - 1||_2 -> 0`, by unitarity and (SH) of
`leavitt-st20-cone-bound-half-rounding-proof`, since a refuting family has `max_i ||ρ_n(k_i) - 1||_2 -> 0`; and
`||σ'_n(z) - 1||_2 = ||ρ_n(z) - 1||_2 + o(1)`, contradicting item 3 (monomial). The dead class includes:
- permutation representations of congruence quotients of `Delta_+-` glued over `Delta_0`;
- Schreier-coset actions;
- representations induced from characters of order dividing `m`.

This is exactly the literal form of the w16 next step 1. What survives are representations whose matrix
coefficients are genuinely non-monomial. By item 4, producing one is a hyperlinear nonsofic group.

The sofic analogue of the whole split is settled: item 3 is the Hamming form of "every asymptotic
representation collapses", so the Hamming forms of `(QC)` and `(HR)` both hold. The unitary split is exactly
the gap between soficity and hyperlinearity for `Delta`.
