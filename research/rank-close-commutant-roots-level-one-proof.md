---
rg: 2
id: rank-close-commutant-roots-level-one-proof
kind: route
title: The perturbations miss a large tensor slice, whose rank-one operators commute with the perturbed constants, so a commutant-compatible root is a tensor product on that slice
target: rank-close-commutant-roots-restrict-to-level-one-roots
requires: [etale-roots-lie-in-the-bicommutant-of-the-constants]
---

Notation as in the claim. Put `E_j = a'_j - a_j (x) 1_r`, so `rank E_j = rho_j`,
and identify `L^{nr}` with `L^n (x) L^r`. Let `e_1, ..., e_n` be the standard
basis of `L^n`, and write `rho = rho_1 + ... + rho_k`.

**Step 1 (a slice inside every kernel).** For each `j` put
`S_j = { s in L^r : E_j (xi (x) s) = 0 for all xi in L^n }`. It is the common kernel
of the `n` linear maps `s |-> E_j (e_p (x) s)`, `p = 1, ..., n`. Each has image
inside `range E_j`, of dimension `rho_j`, so `codim S_j <= n rho_j`. Put
`S_1' = S_1 cap ... cap S_k`. Then `codim S_1' <= n rho`, and
`L^n (x) S_1'` lies in every `ker E_j`.

**Step 2 (a slice containing every range).** Choose a basis `v_1, ..., v_{rho_j}` of
`range E_j` and write `v_i = sum_p e_p (x) s_{ip}` with `s_{ip}` in `L^r`. Let `S_2` be
the span of all `s_{ip}` over all `j`, `i` and `p`. Then `dim S_2 <= n rho`, and
every `range E_j` lies in `L^n (x) S_2`.

**Step 3 (rank-one operators in the commutant).** Since `n rho < r`, `S_1' != 0`
and `S_2 != L^r`. Let `u` be in `S_1'`, and let `phi` be a nonzero linear functional
on `L^r` vanishing on `S_2`. Put `X = 1_n (x) (u phi)`, where `u phi` is the rank-one
map `s |-> phi(s) u`. For every `j`:
- `X E_j = 0`, because `range E_j` lies in `L^n (x) S_2`, which `X` kills;
- `E_j X = 0`, because `range X` lies in `L^n (x) u`, which lies in `ker E_j`;
- `X (a_j (x) 1_r) = a_j (x) u phi = (a_j (x) 1_r) X`.

So `X a'_j = a'_j X`, and `X` is in `C(a')`.

**Step 4 (the root is a tensor product on the slice).** Let `T` be a
commutant-compatible root. Fix `u` in `S_1'`, a functional `phi` as in Step 3, and
`eta` in `L^r` with `phi(eta) = 1`. For `xi` in `L^n`, `TX = XT` applied to
`xi (x) eta` gives

```text
T (xi (x) u) = T X (xi (x) eta) = X T (xi (x) eta)  in  L^n (x) u .
```

So there is a linear map `t_u` of `L^n` with `T (xi (x) u) = t_u(xi) (x) u` for all
`xi`. If `u, u'` in `S_1'` are linearly independent, comparing
`T (xi (x) (u + u'))` with `t_u(xi) (x) u + t_{u'}(xi) (x) u'` gives
`t_u = t_{u + u'} = t_{u'}`. So there is one `t` with `T = t (x) 1` on
`L^n (x) S_1'`; if `dim S_1' = 1`, take `t = t_u`. Since `T` is injective, `t` is
injective, hence `t` is in `GL_n(L)`.

**Step 5 (invariance and the level-one root).** Put `S = S_1'`.
- By Step 1, `a'_j (xi (x) s) = a_j xi (x) s` for `s` in `S`. So `a'_j` maps
  `L^n (x) S` bijectively onto itself and acts there as `a_j (x) 1_S`. The same
  holds for `a'_j^{-1}`, as `a_j^{-1} (x) 1_S`.
- By Step 4, `T` maps `L^n (x) S` bijectively onto itself as `t (x) 1_S`, so
  `T^{-1}` acts there as `t^{-1} (x) 1_S`.
- Every letter of `w` preserves `L^n (x) S`, so `w(T ; a')` acts on it as
  `w(t ; a) (x) 1_S`. Since `w(T ; a') = 1` and `S != 0`, `w(t ; a) = 1`.

Also `dim S >= r - n rho`. This proves Theorem K.

**Step 6 (Corollaries L and M).** Theorem G of
`etale-roots-lie-in-the-bicommutant-of-the-constants` says that an etale root
commutes with every matrix commuting with the constants, so it is
commutant-compatible. Under `rho_j <= delta n r` with `delta < 1/(k n^2)` one has
`n rho <= k n^2 delta r < r`, and Theorem K applies. Corollary M is the
contrapositive, together with the trivial root `t (x) 1_r` when `w(t ; a) = 1`.

**Exact check.** `research/artifacts/hl-kl-rank-density-2026-09-14.md` records
an exact rational check of Step 3 for `n = 2`, `r = 6`, `a = [[2,1],[1,1]]`,
`b = 1 + E_12` and a rank-one perturbation of `b (x) 1_6`. The operator
`X = 1_2 (x) u phi` commutes with both perturbed constants, and a control `u`
outside `S_1'` does not.
