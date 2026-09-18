---
rg: 2
id: kl-kernel-compact-unitary-width-radical-proof
kind: route
title: Evaluate the killing identity at a Gerstenhaber--Rothaus root, and select one width pattern inside the ultrafilter
target: kl-kernel-lies-in-the-compact-unitary-width-radical
requires:
  - nonsingular-equations-preserve-matrix-certificates
artifacts:
  - research/artifacts/nonsingular-equations-and-approximation-radicals.md
---

The one imported input is the root theorem of
`nonsingular-equations-preserve-matrix-certificates`. For every `d >= 1` and every
coefficient tuple `U in U(d)^S`, a word `w(S, t)` with nonzero `t`-exponent sum has a root
`T in U(d)` with `w(U, T) = I`. Note that `U` is arbitrary here and need not satisfy any
relator. Everything else below is elementary.

## (A) The finitary certificate

Suppose `a in F(S)` dies in `(Gamma * <t>)/<<w>>`. Then `a` lies in the normal closure of
`R u {w}` in `F(S u {t})`, so there is an identity in the free group

```text
a = prod_(j=1..A+B) v_j f_j^(eps_j) v_j^(-1),     v_j in F(S u {t}),  eps_j = +-1,
```

where `A` of the `f_j` lie in a finite `R_0 <= R` and the other `B` equal `w`.

Fix `d` and `U in U(d)^S`, and choose a root `T` with `w(U, T) = I`. Evaluate the identity at
`(U, T)`. This is a homomorphism `F(S u {t}) -> U(d)`, and `a` does not involve `t`.

- Each factor with `f_j = w` becomes `v_j(U,T) I v_j(U,T)^(-1) = I` and drops out.
- Each factor with `f_j = r in R_0` becomes `g r(U)^(eps_j) g^(-1)` with `g = v_j(U,T) in U(d)`.

So `a(U)` is a product of `A` conjugates of `r(U)^(+-1)`, `r in R_0`, which is (CW1). The
constants `(R_0, A)` depend only on the identity, not on `d` or `U`. So every killed old
word has bounded compact unitary width, and `ker(Gamma -> H) <= Rad_cw(Gamma)`, once (B)
shows that `Rad_cw` is well defined.

**Where nonsingularity is used.** Only in the existence of `T`. The singular control
`Gamma = C_2`, `w = t a t^(-1)` has `a = t^(-1) w t` with `A = 0`, and `a(U) != I` for
`U = -I`. So the root step cannot be removed.

## (B) Width equals the ultraproduct-quotient radical

Let `P = prod_(i in I) U(d_i)` and let `omega` be an ultrafilter on `I`, with
`N_omega = { x in P : {i : x_i = I} in omega }`. This is a normal subgroup.

**(i) => (ii).** Let `a` have width constants `(R_0, K)`. Let `N >= N_omega` be normal in `P`
and let `phi : Gamma -> P/N` be a homomorphism.

1. Lift each `phi(s)` to `U_s in P`. The tuple `U^(i) = (U_s)_i` is a coefficient tuple in
   `U(d_i)`. For `r in R`, `r(U)` lies in `N`, and coordinatewise `a(U)_i = a(U^(i))`.
2. For each `i`, (i) writes `a(U^(i)) = prod_(k=1..K) g_(i,k) c_(i,k) g_(i,k)^(-1)`, where each
   `c_(i,k)` is either `I` or `r(U^(i))^(+-1)` for some `r in R_0`. Pad short products with
   `I`. The **pattern** of `i` is the sequence of symbols `(r, +-1)` or `empty` for
   `k = 1..K`. There are at most `(2|R_0| + 1)^K` patterns, so `I` is a finite disjoint union
   of pattern classes, and exactly one class `J` lies in `omega`.
3. Let `(c_1, ..., c_K)` be the pattern of `J`, read as elements `c_k in { I } u R_0(U)^(+-1)`
   of `P`. Define `g_k in P` by `(g_k)_i = g_(i,k)` for `i in J` and `I` otherwise. Then
   `x = prod_k g_k c_k g_k^(-1)` lies in `N`, because each `c_k` is `I` or a relator image
   in `N`, and `N` is normal.
4. For `i in J`, `x_i = a(U^(i)) = a(U)_i`. So `a(U) x^(-1) in N_omega <= N`, hence
   `a(U) in N`, and `phi(a) = 1`.

**(ii) => (i).** Suppose (i) fails for `a`. Enumerate `R = {r_1, r_2, ...}`, repeating
entries if `R` is finite, and let `R_m = {r_1, ..., r_m}`. Failure of (i) gives, for every `m`,
a dimension `d_m` and a tuple `U_m in U(d_m)^S` with

```text
a(U_m) notin Cons_m(R_m(U_m)).
```

1. Let `P = prod_(m >= 1) U(d_m)`, let `omega` be a nonprincipal ultrafilter on `N`, and put
   `U = (U_m)_m in P^S` and `N = <<{ r(U) : r in R }>>_P . N_omega`. This is a product of two
   normal subgroups, so it is normal, and `N >= N_omega`.
2. `s |-> U_s N` kills every relator, so it defines `phi : Gamma -> P/N`. By (ii),
   `a(U) in N`.
3. Write `a(U) = y z` with `z in N_omega` and `y` a finite product of `L` conjugates in `P` of
   `r(U)^(+-1)`, with every `r` in some `R_M`. Then for `omega`-almost every `m`,
   `a(U_m) = y_m in Cons_L(R_M(U_m))`.
4. Because `omega` is nonprincipal, that set contains some `m >= max(L, M)`. There
   `Cons_L(R_M(U_m)) <= Cons_m(R_m(U_m))`, which contradicts the choice of `U_m`.

**Consequences of (B).** Condition (ii) does not mention the presentation. So the set of
words of bounded width is the full preimage of the normal subgroup

```text
Rad_cw(Gamma) = intersection of ker(phi) over all phi : Gamma -> P/N,  N >= N_omega.
```

In particular it is a union of cosets of `<<R>>`, and `Rad_cw` does not depend on the
presentation. With (A) this gives `ker(Gamma -> H) <= Rad_cw(Gamma)`.

## (C) Invariant lengths

**Forward.** Let `l_d` be conjugation-invariant, symmetric and subadditive with `l_d(I) = 0`.
If `a(U) = prod_(k <= K) g_k c_k g_k^(-1)`, subadditivity, invariance and symmetry give

```text
l_d(a(U)) <= sum_k l_d(c_k) <= K max_(r in R_0) l_d(r(U)),
```

which is (CW2).

**Converse.** Fix `d` and `U`, and let `l(g) = min{ k : g in Cons_k(R_0(U)) }`, or `+infinity`
if there is no such `k`. Then `l(I) = 0`. The inverse of a product of conjugates of relator
images is again such a product, so `l` is symmetric. Conjugating a product of conjugates
gives another, so `l` is conjugation-invariant. Concatenating products gives subadditivity.
Each `r in R_0` has `l(r(U)) <= 1`, so (CW2) gives `l(a(U)) <= K`, that is,
`a(U) in Cons_K(R_0(U))`. Since `d` and `U` were arbitrary, this is (i).

## Consequences recorded in the target

- **Subadditive lengths.** Operator norm, normalized or unnormalized Hilbert--Schmidt norm,
  Schatten-`p` norm and rank of `g - I` are all subadditive because
  `gh - I = g(h - I) + (g - I)`, and unitarily invariant norms and rank are invariant under
  multiplication by `g`.
- **Radical inclusions.** Every metric ultraproduct of the `U(d_i)` with one of these lengths
  is `P/N` with `N >= N_omega`. So (B) gives `Rad_cw <= Rad_hyp`, and also the rank and
  Schatten radicals. For `Rad_MF`, a unitary of `prod M_(d_i) / (+) M_(d_i)` lifts to a
  sequence of near-unitaries, which polar decomposition corrects to unitaries modulo
  `(+) M_(d_i)`. Operator-norm (CW2) then kills `a`.
- **Simple dichotomy.** If `Gamma` is simple, the normal subgroup `Rad_cw(Gamma)` is `1` or
  `Gamma`.
  - If it is `1`, some `phi` is nontrivial, hence injective, and
    `nonsingular-adjunction-preserves-approximation-radicals` extends `phi` across every
    nonsingular equation. So Kervaire--Laudenbach holds over `Gamma`. Alternatively, (A)
    gives `ker <= Rad_cw = 1` directly.
  - If it is `Gamma`, every element has bounded width.
- **Monotonicity.** For `Gamma <= Delta`, homomorphisms from `Delta` restrict, so
  `Rad_cw(Gamma) <= Rad_cw(Delta) cap Gamma`.

## Limitation

The pattern-selection step 2 of (i) => (ii) needs `N >= N_omega`. For a general normal
`N <= P`, restricting a product to one pattern class need not stay in `N`. Take `P = U(1)^2`
and `N` the diagonal: `(z, z) in N`, but `(z, 1) notin N` for `z != 1`. So this route does not
decide whether `Rad_cw` equals the radical over all quotients of products of unitary groups.
