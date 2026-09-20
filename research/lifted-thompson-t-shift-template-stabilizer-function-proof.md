---
rg: 2
id: lifted-thompson-t-shift-template-stabilizer-function-proof
kind: route
title: Conjugate each arc commutator by u_a^(-1) and sigma^(-1), read the class of d through the interval d(sI), and bound f by splitting at c or at kappa
target: lifted-thompson-t-shift-template-area-is-a-stabilizer-function
requires:
  - lifted-thompson-t-template-envelope-contains-shift-graphs
  - bounded-area-commuting-conjugator-localization
  - lifted-thompson-t-mf-radical-dichotomy
---

This is a complete direct proof.  It uses three inputs:

- two standard facts about Dehn area;
- the data and checks 2–3 of `lifted-thompson-t-template-envelope-shift-graph-proof`;
- `bounded-area-commuting-conjugator-localization`, used only in item 5.

**Area facts.**  For words `w, w'` and `g`:

- (A1) If `w` and `w'` are freely equal, then `Area(w) = Area(w')`.
- (A2) `Area(g w g^(-1)) = Area(w)`.
- (A3) `Area(w w') <= Area(w) + Area(w')`.

Each follows at once from writing a null word as a free product of conjugates of relators.

## Item 1

For the arc `a -> b`,

```text
[C_b, H_a] = u_b c u_b^(-1) · u_a h u_a^(-1) · u_b c^(-1) u_b^(-1) · u_a h^(-1) u_a^(-1).
```

Conjugating by `u_a^(-1)` gives, freely, `[kck^(-1), h]` with `k = u_a^(-1) u_b`.  Freely
`k = σ δ_ab`, and

```text
[σ X σ^(-1), h] = σ [X, σ^(-1) h σ] σ^(-1)    freely,  with X = δ_ab c δ_ab^(-1).
```

(A1) and (A2) then give the equality.  The inequality holds because `δ_ab` is one word for
`d_ab`.

By check 3 of the envelope proof:

- `k|_I = s|_I` (the affine map onto `sI`) and `k|_K = s|_K` (the affine map onto `sK`), so
  `d_ab = s^(-1) k` fixes `I ∪ K` pointwise;
- `kck^(-1) = c_{sI} = scs^(-1)`, hence `d_ab ∈ C(c)`;
- `k^(-1)hk = c_K = s^(-1)hs`, hence `d_ab ∈ C(c_K)`.

Finally, `c` and `c_K` have disjoint supports, so they commute.  Both lie in `D`, and every
element of `D` commutes with both, so they are central in `D`.

## Item 2

Let `δ` be a word for `d` and put `δ' = kappa^p δ c^q`, a word for `c_K^p d c^q`.  Freely,
`δ' c δ'^(-1) = kappa^p (δcδ^(-1)) kappa^(-p)`.  With `X = δcδ^(-1)`, freely

```text
[kappa^p X kappa^(-p), kappa] = kappa^p [X, kappa] kappa^(-p).
```

So `f(c_K^p d c^q) <= f(d)`.  Applying the same to `-p, -q` gives equality.

## Item 3

Write `b_m = (j,l,m)` for `m > l`, and `d_m = d_{a b_m}`.  Then
`d_m(sI) = s^(-1) t_a^(-1) t_{b_m}(sI) = s^(-1) t_a^(-1)(alpha_m)`.

**The intervals are distinct.**  They are pairwise distinct because the `alpha_m` are and
`s^(-1) t_a^(-1)` is a bijection.

**Where they lie.**

- `alpha_m ⊂ E_m`, and `E_m` lies to the left of `alpha_l ⊂ E_l` because `m > l`.
- `t_a` is increasing and maps `sI = [1/16, 1/8]` onto `alpha_l`.  So
  `t_a^(-1)(alpha_m) ⊂ [0, 1/16)`.
- `s` is increasing with `s(5/16) = 1/16`.  So `s^(-1)([0, 1/16)) = [0, 5/16)`.

Hence `d_m(sI) ⊂ [0, 5/16)`.

**Why this is a class invariant.**  The interval `[0, 5/16)` is disjoint from
`int I = (5/16, 3/8)` and from `int K`.  The supports of `c` and `c_K` are `int I` and `int K`
(modulo `Z`, in the lifted picture), so both fix `[0, 5/16)` pointwise.  Also `c^q` fixes `sI`
pointwise.

Suppose `d_m' = c_K^p d_m c^q`.  Then

```text
d_m'(sI) = c_K^p(d_m(sI)) = d_m(sI).
```

So distinct `m` give distinct classes in `D/<c,c_K>`.

## Item 4

By item 1, `sup_m Area([C_{b_m}, H_a]) >= sup_m f(d_m)`.  The `d_m` have pairwise distinct
`d_m(sI)`, so this supremum is infinite if `f` is interval-proper.  If `f` is proper on
`D/<c,c_K>`, the supremum is infinite too, because by item 3 the classes of the `d_m` are
infinitely many.  In both cases (CCC2) fails at the vertex `a`.

None of this depends on the words `u_v`, or on the parts of the `t_v` that are left free, since
every choice gives such an out-star.

## Item 5

**The upper bound.**  Let `δ` be a word for `d` and put `X = δcδ^(-1)`, `Y = Xc^(-1)`.

*Splitting at `c`.*  Freely,

```text
[X, kappa] = Y · [c, kappa] · kappa Y^(-1) kappa^(-1).
```

By (A2) and (A3), `Area([X,kappa]) <= 2 Area(Y) + A_1`.  Minimising over `δ` gives the bound
with `a`.

*Splitting at `kappa`.*  Put `W = δ^(-1) kappa δ kappa^(-1)`.  Freely,

```text
[X, kappa] = δ c W c^(-1) δ^(-1) · δ [c, kappa] δ^(-1) · δ kappa δ^(-1) kappa^(-1),
```

and `δ kappa δ^(-1) kappa^(-1) = δ (W^(-1)) δ^(-1)` freely.  So
`Area([X,kappa]) <= 2 Area(W) + A_1`.  Minimising gives the bound with `b`.

By item 2, both bounds may be applied to any representative `c_K^p d c^q`.

**The lower comparison.**  By the computation of item 2 with `δ = kappa^q` and `d = 1`,
`f(c_K^q) <= Area([c, kappa]) = A_1`.

Suppose instead that `a(c_K^q) <= A` for infinitely many `q`.  `T̄` is torsion-free and
finitely presented.  So `bounded-area-commuting-conjugator-localization`, applied with the
word `y = δ` and commuting partner `c`, gives `c_K^q = c^{n_q} g_q` with `|g_q| <= AM + 2|c|`.

The elements `g_q = c^{-n_q} c_K^q` are pairwise distinct for distinct `q`.  The reason is
that `<c, c_K> ≅ Z^2`: the two elements have disjoint supports and are of infinite order.  But
infinitely many distinct `g_q` cannot lie in a finite ball.  Hence `a(c_K^q) -> infinity`.
