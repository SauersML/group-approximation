---
rg: 2
id: twisted-lef-tower-order-budget-proof
kind: route
title: Proof that phi-twisted LEF towers of subexponential order kill compression defects, by Lagrange's theorem along the twisted layers
target: twisted-lef-tower-order-budget-kills-compression-defects
requires: []
artifacts:
  - research/twisted-lef-tower-order-budget-kills-compression-defects.md
---

Self-contained and elementary.  Notation is as in the target.

## 0. Reduction to one compressor

Write `C = C_G(L)`.  For `s` in `Comp_G(L)` we always have
`s^-1 C s <= C`.  Indeed, `s^-1 z s` commutes with `l` iff `z` commutes
with `s l s^-1`, and `s l s^-1` lies in `L`.

So if `s C s^-1 <= C` for every compressor `s`, then every compressor
normalizes `C`.  Hence `<Comp_G(L)>` normalizes `C`, every generator
`[g z g^-1, l]` is trivial, and `D_G(L) = 1`.

It therefore suffices to show `[s z s^-1, l] = 1` for one compressor `s`,
one `z` in `C`, and `l` in the finite generating set `S_L`.

## 1. The relations in K

Write `s = k t^a` and `z = k' t^b` with `k, k'` in `K`.  For each `l` in
`S_L` fix a word `w_l` in `S_L^(+-1)` with

    k phi^a(l) k^-1 = s l s^-1 = w_l(S_L)                 (R1)
    k' phi^b(l) k'^-1 = z l z^-1 = l                      (R2)

Put `g_l = s^-1 l s = phi^(-a)(k^-1 l k)`, an element of `K`.  The
target is `z g_l z^-1 = g_l`, that is

    k' phi^b(g_l) k'^-1 = g_l.                            (GOAL)

`(GOAL)` is equivalent to `[z, s^-1 l s] = 1`, which is equivalent to
`[s z s^-1, l] = 1`.

Let `B_0` be the finite subset of `K` made of `1`, `S_L^(+-1)`,
`k^(+-1)` and `k'^(+-1)`, together with, for each `l` in `S_L`:

- `phi^a(l)`, `phi^b(l)`, `g_l` and `phi^b(g_l)`;
- every prefix, evaluated in `K`, of each of the words
  `k . phi^a(l) . k^-1`, `w_l`, `k^-1 . l . k`, `k' . phi^b(l) . k'^-1`
  and `k' . phi^b(g_l) . k'^-1`.

A local embedding on `B_0` takes each of these products to the product of
the images of its letters.  It also sends `1` to `1`, since
`iota(1) = iota(1) iota(1)`, and sends inverses to inverses.

## 2. Layers

Fix `iota : K -> F` as in (OB1).  For an integer `m` put

    rho_m = iota o phi^(-m),   A_m = rho_m(S_L),   Pi_m = < A_m > <= F.

Call `m` *good* if `rho_m` is a local embedding on `B_0`.  By hypothesis
every `m` in `I = [0, P)` is good.  Two identities hold exactly, for all
`m` and all `g` in `K`, straight from the definition:

    rho_m(g) = rho_(m+a)(phi^a(g)),   rho_m(g) = rho_(m+b)(phi^b(g)).   (SH)

For a word `v` in `|S_L|` letters, `v(A_m)` means `v` evaluated at the
tuple `(rho_m(l))_(l in S_L)`.

## 3. The compressor step

Let `m + a` be good.  Put `x = rho_(m+a)(k)` and `c_x(y) = x y x^-1`.
For `l` in `S_L`:

    c_x(rho_m(l)) = x rho_(m+a)(phi^a l) x^-1        by (SH)
                  = rho_(m+a)(k phi^a(l) k^-1)        by the local embedding
                  = rho_(m+a)(w_l)                    by (R1)
                  = w_l(A_(m+a))                      by the local embedding.

Since `c_x` is an automorphism of `F`, we get

    c_x(v(A_m)) = v(w(A_(m+a)))   for every word v,             (C1)

where `v(w(...))` substitutes `w_l` for each letter `l`.  In particular
`c_x(Pi_m) <= Pi_(m+a)`.

**Lagrange step.**  `c_x(Pi_m)` is a subgroup of `Pi_(m+a)` of order
`|Pi_m|`.  So either `|Pi_(m+a)| = |Pi_m|` and `c_x(Pi_m) = Pi_(m+a)`,
or `|Pi_(m+a)| >= 2 |Pi_m|`.

## 4. The centralizer step

Let `m + b` be good and put `y_m = rho_(m+b)(k')`.  The same computation
with (R2) in place of (R1) gives

    c_(y_m)(rho_m(l)) = rho_(m+b)(l)   for every l in S_L,

hence

    c_(y_m)(v(A_m)) = v(A_(m+b))   for every word v.              (C2)

## 5. A non-strict step forces (GOAL)

**Lemma.**  Suppose `m + a`, `m + b` and `m + a + b` are good, and
`|Pi_m| = |Pi_(m+a)|`.  Then (GOAL) holds for every `l` in `S_L`.

*Proof.*  Fix `l`.  Put `x = rho_(m+a)(k)` and `x' = rho_(m+a+b)(k)`.

(i) By Section 3, `Pi_(m+a) = c_x(Pi_m)`.  So there is a word `v_l` with
`rho_(m+a)(l) = c_x(v_l(A_m))`, which by (C1) at level `m` equals
`v_l(w(A_(m+a)))`.

(ii) By (SH) and the local embedding at `m + a`,
`rho_m(g_l) = rho_(m+a)(k^-1 l k) = x^-1 rho_(m+a)(l) x = v_l(A_m)`.

(iii) Apply `c_(y_(m+a))` to (i), using (C2) at level `m + a`, which
needs `m + a + b` good.  The left side becomes `rho_(m+a+b)(l)` and the
right side becomes `v_l(w(A_(m+a+b)))`.

(iv) (C1) at level `m + b` (again `m + a + b` good) gives
`c_(x')(v_l(A_(m+b))) = v_l(w(A_(m+a+b))) = rho_(m+a+b)(l)`, by (iii).

(v) As in (ii), at level `m + a + b`:
`rho_(m+b)(g_l) = x'^-1 rho_(m+a+b)(l) x' = v_l(A_(m+b))`, by (iv).

(vi) (C2) at level `m` applied to (ii) gives
`c_(y_m)(rho_m(g_l)) = v_l(A_(m+b)) = rho_(m+b)(g_l)`, by (v).

By (SH) and the local embedding at `m + b`, the left side is

    y_m rho_(m+b)(phi^b g_l) y_m^-1 = rho_(m+b)(k' phi^b(g_l) k'^-1).

So `rho_(m+b)` takes the same value on `k' phi^b(g_l) k'^-1` and on
`g_l`.  Both elements lie in `B_0`, and `rho_(m+b)` is injective on
`B_0`, so they are equal.  That is (GOAL).  QED

The words `v_l` may be arbitrarily long.  They are never lifted to `K`:
only the fixed finite set `B_0` is ever evaluated there.  This is where
the finite-group order is spent.

## 6. The chain count: proof of (OB1)

Let `N = floor(log_2 |F|) + 1`, so `2^N > |F|`.

**Case a = 0.**  Here `Pi_(m+a) = Pi_m` for every `m`, so every step is
non-strict.  Take `m = max(0, -b)`.  Then `m` and `m + b` both lie in
`[0, |b|]`, which is inside `I`, and the Lemma applies.

**Case a > 0.**  Put `m_0 = max(0, -b)` and `m_i = m_0 + i a` for
`0 <= i <= N`.  For each `i < N`, the layers `m_i + a`, `m_i + b` and
`m_i + a + b` lie in `[0, |b| + N a]`, which is inside `I` because
`P >= N|a| + |b| + 1`.

If every step `m_i -> m_(i+1)` were strict, Section 3 would give
`|Pi_(m_N)| >= 2^N |Pi_(m_0)| >= 2^N > |F|`, which is impossible.  So
some step is non-strict, and the Lemma at `m = m_i` gives (GOAL).

**Case a < 0.**  Run the same argument with
`m_0 = P - 1 - max(0, b)` and `m_i = m_0 - i|a|`.  All the layers used
lie in `[P - 1 - |b| - N|a|, P - 1]`, which is inside `I`.

Finally (GOAL) for all `l` in `S_L` gives `[s z s^-1, l] = 1` for all
`l` in `L`.  QED (OB1)

## 7. (OB2), (OB3), (OB4)

**(OB2).**  The case `a = 0` above used only the layers `m` and `m + b`.
With `m = 0`, this needs only that `iota` is a local embedding on
`B_0 union phi^(-b)(B_0)`.  If `K` is LEF, such an `iota` exists.  Hence
`s C s^-1 <= C` for every compressor `s` in `K`.

**(OB3).**  Fix a finitely generated `L <= K`, a compressor `s`, and
`z` in `C`.  The set `B_0` is finite.  By (SUB) there are `P_j -> infinity`
with `beta_phi(B_0, P_j) <= P_j / (4(|a| + 1))`.

For large `j` this gives

    (floor(beta) + 1)|a| + |b| + 1  <=  P_j/4 + |a| + |b| + 1  <=  P_j.

So (OB1) applies.  Section 0 then gives `D_G(L) = 1`.

A Kazhdan `L <= G` is finitely generated and has finite abelianization.
Its image in `G/K = Z` is therefore trivial, so `L <= K`.

**(OB4).**  Suppose `D_G(L) != 1`.  By Section 0 some compressor
`s = k t^a`, some `z` in `C` and some `l` in `S_L` have
`[s z s^-1, l] != 1`.  If `K` is LEF, then `a != 0` by (OB2).

By (OB1), every admissible `(F, iota, P)` for `B_0` then has
`P < (floor(log_2 |F|) + 1)|a| + |b| + 1`.  This gives
`log_2 |F| > (P - |b| - 1)/|a| - 1`, so (SUB) fails for `B_0`.  QED
