---
rg: 2
id: fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction-proof
kind: route
title: Schreier counting, inverse limits and a central procyclic subgroup settle the bounded-type reduction
target: fpbs-fg-by-cyclic-farber-chains-bounded-type-reduction
requires:
  - fpbs-quotient-split-actions-have-cost-one
artifacts:
  - experiments/mapping-torus-inner-quotients-2026-09-17/inner2.g
  - experiments/mapping-torus-inner-quotients-2026-09-17/run2.g
  - experiments/mapping-torus-inner-quotients-2026-09-17/run2.out
---

# Proofs: Farber chains of f.g.-by-cyclic groups and inner profinite completions

Notation. `N` is a finitely generated infinite group, `phi` is in `Aut(N)`, and
`Gamma = N x|_phi Z = <N, t | t x t^-1 = phi(x)>`. A *Farber chain* is a
descending chain `(Gamma_n)` of finite-index normal subgroups with trivial
intersection. `d` is the minimal number of (topological) generators, and
`RG(Gamma,(Gamma_n)) = lim (d(Gamma_n)-1)/[Gamma:Gamma_n]`. The limit exists
by Schreier monotonicity. For a profinite `X` with open normal `U_n`
descending to `1`, `RG(X,(U_n))` is defined the same way with topological `d`.
Write `k_n = [Gamma : Gamma_n N]`, the index of the image of `Gamma_n` in
`Gamma/N = Z`.

## 1. Dichotomy

**Lemma 1.1.** `k_n` divides `k_{n+1}`, so `(k_n)` is non-decreasing.

*Proof.* `Gamma_{n+1} N <= Gamma_n N`. []

**Proposition 1.2 (unbounded type).** If `k_n -> infinity`, then
`RG(Gamma,(Gamma_n)) = 0`.

*Proof.* Put `K_n = Gamma_n ∩ N`. It is normal of finite index in `N`, with
`[N:K_n] = [Gamma_n N : Gamma_n] = [Gamma:Gamma_n]/k_n`. The group
`Gamma_n/K_n ≅ Gamma_n N/N = k_n Z` is cyclic, so `d(Gamma_n) <= d(K_n)+1`.
Schreier's formula gives `d(K_n) <= (d(N)-1)[N:K_n] + 1`. Therefore
`(d(Gamma_n)-1)/[Gamma:Gamma_n] <= (d(N)-1)/k_n + 1/[Gamma:Gamma_n] -> 0`. []

**Proposition 1.3 (reduction to inner type).** Suppose `k_n` is bounded, hence
equal to some `k` for `n >= n_0`. Put `Gamma' = N x| <t^k>`, which is
`N x|_{phi^k} Z`. Then `Gamma_n <= Gamma'` for `n >= n_0`, each `Gamma_n` is
normal in `Gamma'`, `N` maps onto `Gamma'/Gamma_n`, and
`RG(Gamma,(Gamma_n)) = RG(Gamma',(Gamma_n)_{n>=n_0}) / k`.

*Proof.* For `n >= n_0` we have `Gamma_n N = Gamma'`, which has index `k` in
`Gamma`. So `N Gamma_n = Gamma'`, which is surjectivity of `N -> Gamma'/Gamma_n`.
The index relation is `[Gamma:Gamma_n] = k [Gamma':Gamma_n]`. []

Call a chain with `k_n = 1` for all `n` *inner type*. By 1.2 and 1.3, a
Farber chain of `N x|_phi Z` with positive rank gradient exists only if, for
some `k >= 1`, the finite-index subgroup `N x|_{phi^k} Z` has an inner-type
Farber chain with positive rank gradient. Conversely an inner-type chain of
positive gradient in `N x|_{phi^k} Z` is already a positive-gradient Farber
chain of an f.g.-by-cyclic group, so for the counterexample question the two
classes of chains are interchangeable.

## 2. Inner completion

**Proposition 2.1.** Let `(Gamma_n)` be an inner-type Farber chain of
`Gamma = N x|_phi Z`. Let `X = lim Gamma/Gamma_n`, let `iota : Gamma -> X` be
the canonical map, `U_n = ker(X -> Gamma/Gamma_n)` and `g = iota(t)`. Then:

- (a) `iota` is injective, and `iota(N)` is dense in `X`.
- (b) `iota(phi(x)) = g iota(x) g^-1` for every `x` in `N`.
- (c) `g^j` is not in `iota(N)` for `j != 0`.
- (d) The `U_n` are open, normal, descending, with `∩ U_n = 1` and `[X:U_n] = [Gamma:Gamma_n]`.
- (e) `RG(Gamma,(Gamma_n)) >= RG(X,(U_n))`.

*Proof.*
- (a) `ker iota = ∩ Gamma_n = 1`. `N` surjects onto every `Gamma/Gamma_n = X/U_n`.
- (b) This is `t x t^-1 = phi(x)`.
- (c) `g^j = iota(x)` would give `t^j = x` in `N` by injectivity, so `j = 0`.
- (d) This is standard for inverse limits of surjections.
- (e) `iota(Gamma_n) = iota(Gamma) ∩ U_n` is dense in the open set `U_n`, since
  `iota(Gamma)` is dense. Hence `d(U_n) <= d(Gamma_n)`. []

## 3. Converse construction (the criterion)

**Theorem 3.1.** Let `N` be f.g. infinite and `psi` in `Aut(N)`. Let `X` be a
profinite group with an injective homomorphism `iota : N -> X` with dense image
and an element `g` in `X` such that

- (i) `iota(psi(x)) = g iota(x) g^-1` for every `x` in `N`, and
- (ii) `g^j` is not in `iota(N)` for `j != 0`.

Let `U_n` be open normal subgroups of `X`, descending, with `∩ U_n = 1`. Then,
for `Gamma = N x|_psi <s>`:

- the map `iota~(x s^j) = iota(x) g^j` is an injective homomorphism `Gamma -> X` with dense image;
- `Gamma_n := iota~^-1(U_n)` is an inner-type Farber chain with `[Gamma:Gamma_n] = [X:U_n]`;
- `RG(Gamma,(Gamma_n)) >= RG(X,(U_n))`.

*Proof.*
- *Homomorphism.*
  `iota~((x s^i)(y s^j)) = iota~(x psi^i(y) s^{i+j}) = iota(x) g^i iota(y) g^-i g^{i+j} = iota~(x s^i) iota~(y s^j)`,
  using (i) iterated.
- *Injective.* `iota(x) g^j = 1` gives `g^j` in `iota(N)`. By (ii) `j = 0`,
  and then `x = 1`.
- *Dense.* The image contains `iota(N)`.
- *Index.* `Gamma_n` is normal. It has index `[X:U_n]`, since the dense image
  surjects onto `X/U_n`.
- *Trivial intersection.* `∩ Gamma_n = iota~^-1(1) = 1`.
- *Inner type.* `N` maps onto `X/U_n` by density of `iota(N)`.
- *Gradient.* The inequality follows as in 2.1(e). []

**Corollary 3.2 (counterexample criterion).** In the setting of 3.1, if
`RG(X,(U_n)) > 0`, then `Gamma` is a countable group with two essentially free
p.m.p. actions of different costs.

More generally, it is enough to have a dense f.g. subgroup `Gamma <= X` with
`cost(Gamma) = 1` (infimal cost) and `RG(X,(U_n)) > 0`.

*Proof.*
- Action 1. Put `Gamma_n = Gamma ∩ U_n`, a Farber chain. By Abért–Nikolov
  (Rank gradient, cost, and residual finiteness), the boundary action of
  `Gamma` on `lim Gamma/Gamma_n` with Haar measure is free, with cost
  `1 + RG(Gamma,(Gamma_n)) >= 1 + RG(X,(U_n)) > 1`.
- Action 2. For `Gamma = N x| Z`, apply Theorem A of
  `fpbs-quotient-split-actions-have-cost-one` with `K = d(N)` and `Q = Z`,
  where `sigma` is an irrational rotation (free, cost 1). For any free action
  `beta` of `Gamma`, the diagonal action `beta x sigma` is free and has cost 1. []

## 4. Obstructions to the criterion

**Proposition 4.1.** Let `X` be topologically finitely generated. Suppose `X`
has an infinite closed normal subgroup `C` that is abelian and topologically
generated by `r` elements. Then `RG(X,(U_n)) = 0` for every descending chain of
open normal `U_n` with `∩ U_n = 1`.

*Proof.*
- The group `U_n ∩ C` is an open subgroup of `C`, and `C` is a quotient of
  `Zhat^r`. Its preimage there is an open subgroup of `Zhat^r`, which is
  isomorphic to `Zhat^r`. So `d(U_n ∩ C) <= r`.
- `U_n/(U_n ∩ C) ≅ U_n C/C` is a quotient of `U_n C`, which is open of index
  `m_n = [X:U_n C]`. By the profinite Schreier bound,
  `d(U_n C) <= (d(X)-1) m_n + 1`.
- Hence `d(U_n) <= r + (d(X)-1) m_n + 1`.
- The index is `[X:U_n] = m_n [C : C ∩ U_n]`, and `[C:C ∩ U_n] -> infinity`
  because `C` is infinite and `∩ (C ∩ U_n) = 1`. So
  `(d(U_n)-1)/[X:U_n] <= (d(X)-1)/[C:C∩U_n] + r/[X:U_n] -> 0`. []

**Corollary 4.2 (calibration: finite-order outer monodromy gives nothing).**
In 3.1, suppose `psi^m = inn(h)` for some `m >= 1` and some `h` in `N`. Then
`RG(X,(U_n)) = 0`.

*Proof.*
- Let `X''` be the closure of `iota~(N x| <s^m>)`. It contains the dense
  subgroup `iota(N)`, so in fact `X'' = X`; we keep the notation only to make
  the argument read the same for non-dense variants.
- Put `z = g^m iota(h)^-1`. For `x` in `N`:
  `z iota(x) z^-1 = g^m iota(h^-1 x h) g^-m = iota(psi^m(h^-1 x h)) = iota(x)`.
  So `z` centralizes the dense subgroup `iota(N)` of `X''` and commutes with
  itself, hence is central in `X''`.
- `z^j = 1` with `j != 0` would put `g^{mj}` in `iota(N)`, contradicting (ii).
  So `C = closure<z>` is infinite procyclic and central in `X''`.
- By 4.1 applied to `X''` with the chain `U_n ∩ X''`, the gradient of `X''` is
  0. Since `U_n <= X''` for large `n`, this gives `RG(X) = RG(X'')/[X:X''] = 0`. []

Calibration. When `psi` is inner, `Gamma ≅ N x Z`. This group has fixed price 1
by Gaboriau (infinite amenable normal subgroup), so the criterion must
yield nothing, and 4.2 confirms it does. Consequently the monodromy must have
infinite order in `Out(N)`.

**Proposition 4.3 (finite-rank completions give nothing).** If `X` has finite
rank, that is `sup_U d(U) < infinity` over open `U` (for example `X`
p-adic analytic), then `RG(X,(U_n)) = 0`. This is immediate.

This covers single-prime congruence completions of arithmetic mapping tori,
such as the figure-eight knot group inside `PSL_2(Z[omega])` completed at one
prime. The discrete gradient `RG(Gamma)` along such chains is not controlled by
this, and remains the open rank-versus-Heegaard-genus problem.

**Proposition 4.4 (standard free subgroups of free pro-p groups fail).** Let
`X = F^_p(2)`, the free pro-p group of rank 2, and let `iota` map `N = F_2`
onto the discrete free group on a topological basis. Then no `(psi, g)`
satisfies (i) and (ii).

*Proof.*
- (i) says that `psi(x)` is conjugate to `x` in `X` for every `x` in `F_2`.
- Free groups are conjugacy p-separable. This is Toinet, *Conjugacy
  p-separability of right-angled Artin groups and applications*, Groups Geom.
  Dyn. 2013, the case of free RAAGs. So `psi(x)` is conjugate to `x` in `F_2`,
  that is, `psi` is class-preserving.
- By Grossman (Proc. LMS 1974), class-preserving automorphisms of free groups
  are inner. So `psi = inn(h)`.
- Then `z = g iota(h)^-1` centralizes `iota(F_2)`, hence is central in `X`.
- The center of `F^_p(2)` is trivial, so `g = iota(h)` lies in `iota(N)`,
  contradicting (ii). []

So in target P the subgroup `N` must be embedded non-standardly. For example,
`iota(N)` might need more than `d(X)` generators, or might not induce the full
pro-p topology on `N`.

## 5. What is and is not proved

Proved:

- 1.2 and 1.3 (bounded type is necessary for positive gradient);
- 2.1 (the translation into profinite data);
- 3.1 and 3.2 (sufficiency of positive profinite gradient);
- 4.1 to 4.4 (obstructions).

Not proved:

- The converse of 3.2. The discrete gradient `RG(Gamma,(Gamma_n))` can exceed
  `RG(X,(U_n))`, so positivity of the discrete gradient does not force
  positivity of the profinite gradient.
- Target P itself: a profinite `X` with a positive-gradient chain containing
  data (i) and (ii) with infinite-order outer monodromy, not of type 4.1, 4.3
  or 4.4.
