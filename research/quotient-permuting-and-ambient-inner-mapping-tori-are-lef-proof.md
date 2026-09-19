---
rg: 2
id: quotient-permuting-and-ambient-inner-mapping-tori-are-lef-proof
kind: route
title: Model the stable letter exactly, either on an invariant finite quotient family or through an ambient LEF conjugator, and pass LEF up a finite-index extension
target: quotient-permuting-and-ambient-inner-mapping-tori-are-lef
requires: []
artifacts:
  - research/quotient-permuting-and-ambient-inner-mapping-tori-are-lef.md
  - research/lef-implies-operator-mf.md
  - research/subshift-diagonal-automorphisms-need-infinite-spatial-class.md
  - research/char-zero-subshift-elementary-group-is-lef-kazhdan-quotientless.md
---

Notation is that of the claim. "Chabauty convergence `L_i -> L`" means: for every `m ∈ M`,
either `m ∈ L_i` for all but finitely many `i`, and then `m ∈ L`, or `m ∈ L_i` for only
finitely many `i`, and then `m ∉ L`.

## 0. Two LEF facts

**0.1 Limits of finite quotients.** Let `Γ` be finitely generated, `ρ_i : Γ -> F_i`
homomorphisms to finite groups, and `ker ρ_i -> N` (Chabauty) with `N ⊴ Γ`. Then `Γ/N` is LEF.

*Proof.* Let `W ⊂ Γ/N` be finite, and pick lifts `w -> w~`. There are finitely many
conditions:
- `w~ w'~ ((w w')~)^-1 ∈ N` whenever `w, w', w w' ∈ W`;
- `w~ (w'~)^-1 ∉ N` whenever `w != w'`.

Each condition holds in `ker ρ_i` for all large `i`. So for large `i`, `w -> ρ_i(w~)` is an
injective partial homomorphism on `W`.

**0.2 Finite-index overgroups.** If `Λ ≤ Γ` has index `m` and `Λ` is LEF, then `Γ` is LEF.

*Proof.* By Kaloujnine--Krasner, `Γ` embeds in `Λ ≀ Sym(m) = Λ^m ⋊ Sym(m)`, and subgroups of
LEF groups are LEF. Let `W ⊂ Λ^m ⋊ Sym(m)` be finite.
- Let `S ⊂ Λ` be the set of coordinates of elements of `W`.
- Choose a finite group `F` and a map `β : S ∪ SS -> F`, injective, with `β(ab) = β(a)β(b)`
  for `a, b ∈ S`.
- Put `B(λ_1, ..., λ_m; π) = (β(λ_1), ..., β(λ_m); π) ∈ F ≀ Sym(m)` on `W ∪ WW`.

For `w = (λ; π)` and `w' = (λ'; π')`, the `i`-th coordinate of `w w'` is
`λ_i λ'_(π^-1 i)`, a product of two elements of `S`. So `B(w w') = B(w) B(w')`. `B` is
injective on `W ∪ WW`, because `β` is injective on `S ∪ SS`.

**0.3 Ultraproducts.** A finitely generated subgroup `Γ` of an algebraic ultraproduct
`prod_ω Γ_k` of LEF groups is LEF. A finite window of `Γ` embeds, as a partial
homomorphism, into `Γ_k` for `ω`-many `k`, and then into a finite group by LEF of `Γ_k`.

Products of two LEF groups are LEF, coordinatewise. `Z` is LEF.

## 1. Proof of (A)

`α(L) = L`: `m ∈ L` iff `m ∈ L_i` for almost all `i` iff `α(m) ∈ α(L_i) = L_i` for almost
all `i` iff `α(m) ∈ L`. So `L × {0}` is normal in `Γ = M ⋊_α Z`, and
`Γ / (L × {0}) = (M/L) ⋊_α Z`.

Let `α_i` be the automorphism of the finite group `E_i = M/L_i` induced by `α`, of order
`o_i`, and put `c_i = i o_i`. Since `α_i^(c_i) = 1`, the map

```text
ρ_i : Γ -> F_i = E_i ⋊_(α_i) Z/c_i Z,     (m, j) -> (m L_i, j mod c_i)
```

is a homomorphism. Take `γ = (m, j)`.
- If `j != 0`, then `ρ_i(γ) != 1` once `c_i ≥ i > |j|`, and `γ ∉ L × {0}`.
- If `j = 0`, then `ρ_i(γ) = 1` iff `m ∈ L_i`, and Chabauty convergence gives the
  dichotomy with limit `L`.

So `ker ρ_i -> L × {0}`, and 0.1 applies. `M` is finitely generated, so `Γ` is too.

## 2. Proof of (B)

*Degenerate case.* If `{N_n}` is finite, some `N_n` recurs infinitely often, and the
Chabauty dichotomy forces the sequence to be eventually constant, equal to `N`. Then `M/N`
is finite and `(M/N) ⋊ Z` is virtually `Z`, hence LEF (residually finite). Otherwise pass to
the pairwise distinct subsequence, which has the same limit.

*Finite orbits.* `M` is finitely generated, so `Hom(M, F)` is finite for every finite `F`.
Every normal subgroup with quotient isomorphic to `F` is the kernel of a surjection
`M -> F`, so there are finitely many of them. `α^j(N_n)` has quotient isomorphic to
`M/N_n` for every `j`, so the `α`-orbit of `N_n` is finite.

*Invariance.* Let `s` be the bijection of the index set with `α(N_n) = N_(s(n))`. It is well
defined because the `N_n` are distinct. A bijection preserves the cofinite subsets and the
finite subsets of the index set. So `m ∈ α(N)` iff `α^-1(m) ∈ N_n` for almost all `n` iff
`m ∈ N_(s(n))` for almost all `n` iff `m ∈ N_k` for almost all `k` iff `m ∈ N`.

*The invariant family.* The `s`-orbits `O_1, O_2, ...` are finite and partition the
infinite index set. Enumerate them by strictly increasing minimum, so `min O_i -> ∞`. The
subgroup `L_i = ⋂_(n ∈ O_i) N_n` is normal, of finite index and `α`-invariant. Fix `m`.
Chabauty gives `n_0` with one of two cases:
- `m ∈ N_n` for all `n ≥ n_0`, when `m ∈ N`;
- `m ∉ N_n` for all `n ≥ n_0`, when `m ∉ N`.

Once `min O_i ≥ n_0`, `m ∈ L_i` in the first case and `m ∉ L_i` in the second, since
`O_i != ∅`. So `L_i -> N`, and (A) applies with `L = N`.

## 3. Proof of (C)

`t^m` acts on `K` by `φ^m = Ad(h)`. Define `ι : K ⋊ mZ -> H × Z` by `ι(k, mn) = (k h^n, n)`.
- It is a homomorphism: `(k, mn)(k', mn') = (k φ^(mn)(k'), m(n+n'))`, and
  `k h^n k' h^(-n) h^(n+n') = (k h^n)(k' h^(n'))`.
- It is injective: `k h^n = 1` and `n = 0` force `k = 1`.

`H × Z` is LEF, so `K ⋊ mZ` is LEF. It has index `m` in `G`, so `G` is LEF by 0.2.

## 4. The applications

**4.1 The test case.** `K = M/N` for a marked limit `N_n -> N` of finite quotients, and `φ`
is induced by `α ∈ Aut(M)` permuting `{N_n}` or a cofinite part of it. Then (B) applies
verbatim. The torsion-free alternating-mother limits of
`torsion-free-kazhdan-alternating-mother-limit-gate` are of this form. So is every other
kernel presented as a marked limit of finite quotients of a finitely generated mother.

**4.2 Linear ambient groups.** Let `Ψ : R -> prod_ω M_(N_k)(A)` be an injective unital ring
map, with `A = F_q` or `A = Z`. It induces an injective homomorphism
`GL_n(R) -> prod_ω GL_(n N_k)(A)`. Each `GL_(nN)(A)` is finite or residually finite,
hence LEF. By 0.3, every finitely generated subgroup of `GL_n(R)` is LEF.

For `R = LC(X,F_q) ⋊ Z` this `Ψ` is §3.2 of
`research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`. For
`R_0 = LC(X,Z) ⋊ Z` it is §2 of `char-zero-subshift-elementary-group-is-lef-kazhdan-quotientless-proof`
(file `research/char-zero-subshift-elementary-group-proof.md`).

Take `K = EL_n(R)` and `H = <K, h>` for the relevant `h ∈ GL_n(R)`.

**4.3 Standard automorphisms.** Let `σ ∈ Aut(R)`. It acts entrywise on `M_n(R)`, on `GL_n(R)`
and on `EL_n(R)`. Let `g ∈ GL_n(R)` normalize `EL_n(R)`, and put `τ = Ad(g) ∘ σ`.
- By induction, `τ^j = Ad(g_j) ∘ σ^j` with `g_j = g σ(g) ... σ^(j-1)(g)`, because
  `σ ∘ Ad(x) = Ad(σ(x)) ∘ σ`.
- If `σ^m = Ad(v)` with `v ∈ R^x`, then `σ^m = Ad(v I_n)` on `M_n(R)`, so
  `τ^m = Ad(h)` with `h = g_m v I_n ∈ GL_n(R)`.
- `h K h^-1 = τ^m(K) = K`, so (C) applies with this `h`.

The case `σ = id`, `m = 1` is conjugation by `g`. Every diagonal matrix of units
`δ = diag(v_1, ..., v_n)` normalizes `EL_n(R)`, since `δ e_ij(r) δ^-1 = e_ij(v_i r v_j^-1)`.

**4.4 Automorphisms of the subshift.** Let `ψ ∈ Aut(X,T)` with `ψ^r = T^s`, `r ≥ 1`. Put
`σ(f) = f ∘ ψ^-1` on `LC(X,A)` and `σ(u) = u`. This respects `u f u^-1 = f ∘ T^-1`, because
`ψ T = T ψ`, so `σ` is a ring automorphism of `LC(X,A) ⋊ Z`. Then:
- `σ^r(f) = f ∘ T^-s = u^s f u^-s`;
- `σ^r(u) = u = u^s u u^-s`.

So `σ^r = Ad(u^s)`, and 4.3 applies.

For diagonal-preserving `σ` of `LC(X,F_q) ⋊ Z` with `φ_σ^r ∈ [[T]]`, item 3 of
`subshift-diagonal-automorphisms-need-infinite-spatial-class` gives `σ^(er(q-1)) = Ad(v)` with
`v ∈ S^x`. Again 4.3 applies.

**4.5 Conclusion.** In every case `G` is LEF. By `lef-implies-operator-mf`, `G` is MF, so
`Rad_MF(G) = 1 != K`.
