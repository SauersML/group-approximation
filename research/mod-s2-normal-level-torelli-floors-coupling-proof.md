---
rg: 2
id: mod-s2-normal-level-torelli-floors-coupling-proof
kind: route
title: Average a single relation over the deck group of a normal level to get the whole multiplicity vector, bound both floors above by constant vectors, and read off Gamma(3) and Gamma(4) from existing census data
target: mod-s2-normal-level-torelli-floors-are-coupled
requires:
  - mod-s2-monomial-torelli-windings-census
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-induced-torelli-characters-have-positive-relation-floors
  - mod-s2-gamma4-torelli-census-is-one-thirtieth
  - mod-s2-finite-image-near-scalar-reps-are-torelli-abelian
artifacts:
  - experiments/mod-s2-normal-level-coupling-2026-09-17/check_normal_levels.py
  - experiments/mod-s2-normal-level-coupling-2026-09-17/normal-levels.json
  - experiments/mod-s2-torelli-scalar-census-2026-09-17/census-results-frame-3.json
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4-results.json
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4-structure.json
---

Notation of the target.

**Step 1: the deck group permutes the classes and preserves W.** Let `Gamma'` be normal in `Gamma`. Then
`M'` is normal in `M`, and `G = M/M'` acts on `H_1(M')` by `x . [y] = [x y x^(-1)]`. Elements of `M'` act
by inner automorphisms, hence trivially.
- Take coset representatives `g_c`. For `x in M`, `x g_c = m' g_(c')` with `m' in M'`, where `c'` is the
  coset of `x g_c`.
- So `x . v_c = [m' (g_(c') t_s g_(c')^(-1)) m'^(-1)] = v_(c')`. The action of `G` on cosets is the left
  regular action, which is simply transitive.
- The map `c -> v_c` is `G`-equivariant. Hence `G` permutes the set of classes transitively, and every
  fiber has the same size `mult_j = |G| / #classes`, so `mult` is constant.
- `x` is an automorphism of `H_1(M')`. So `sum_j w_j v_j = 0` implies `sum_j w_j (x . v_j) = 0`, i.e.
  `G` preserves `W`.
- It therefore preserves `W^* = {h : <w, h> in Z for all w in W}`, acting by `(x . w)_(x.j) = w_j`.

**Step 2: averaging (N1).** Let `w in W`, and let `Stab_j` be the stabilizer of class `j`, of size
`|G| / #classes = mult_j`. Then
```text
( sum_(x in G) x . w )_k  =  sum_j w_j #{x : x . j = k}  =  sum_j w_j |Stab_j|  =  chi(w) mult_k .
```
Let `h in W^*` with `max_j |h_j| < 1/||w||_1`. Each `x . w` lies in `W` and has `||x . w||_1 = ||w||_1`.
So `<x . w, h>` is an integer of absolute value below 1, hence 0. Summing over `x` gives
`chi(w) <mult, h> = 0`.
- If `chi(w) != 0`, then `<mult, h> = 0`.
- So every `h in W^*` with `<mult, h> != 0` has `max |h_j| >= 1/||w||_1`, i.e. `e(Gamma') >= 1/||w||_1`.
- Minimizing over `w` gives `e >= 1/m_0`.

**Step 3: constant vectors (N2).**
- **Winding floor.** `h = (1/g) 1` satisfies `<w, h> = chi(w)/g in Z` for `w in W`, so `h in W^*`. Also
  `<mult, h> = [Gamma : Gamma']/g != 0`. Hence `e <= 1/g`.
- **Cube-root floor.** For `d`, `3 not| g`: this is recorded on `mod-s2-torelli-abelian-census-limit-is-positive`,
  and it also follows directly, since otherwise `theta = (1/3) 1` would be feasible and give `d = 0`,
  against the per-level positivity there. So `g = 3k +- 1` for some integer `k`.
  - The constant `theta = (k/g) 1` satisfies `sum_c w_c theta_c = k chi(w)/g in Z`.
  - It has `||k/g - 1/3|| = 1/(3g)`, so `d <= 1/(3g)`.
- **Lower bound for `d`.** `d >= 1/(3 m_3)` is (TA3), equivalently (RF), which needs no normality.
- **Tight vectors.** A tight vector has `||w||_1 = |chi(w)| = g`, with `3 not| g`. So
  `m_0 <= g <= m_0` and `m_3 = g`, which gives (N3).

**Step 4: the four principal levels (N4).** Each level `Gamma(N)` is normal. The checks below are exact and
are made by `check_normal_levels.py`.
- **`N = 3`.** From `census-results-frame-3.json`:
  - there are 45 classes, each of multiplicity 1152;
  - `gcd_aug = 5`;
  - the certificate `cert_w` lies in the `Z`-span of the stored `W` basis (tested by HNF) and has
    `l1 = 5`, `chi = -5`.

  So it is tight, and `e(Gamma(3)) = 1/5` and `d(Gamma(3)) = 1/15`. The latter agrees with the stored
  distance.
- **`N = 4`.** From `mod-s2-gamma4-torelli-census-is-one-thirtieth` (G3)-(G5): `g = 10`, and a transversal
  relation has `l1 = chi = 10`. So `e(Gamma(4)) = 1/10`.
  - For `Gamma(4) <= Gamma' <= Gamma(2)`, (MW2) gives `1/10 = e(Gamma(4)) <= e(Gamma') <= e(Gamma(2)) = 1/10`.
  - For every `Gamma' >= Gamma(4)`, (MW2) gives `e(Gamma') >= 1/10`.
- **`N = 1, 2`.** From the (MW4) and (TA4) tables: `W = 5Z` on one class, and `W = Z 1` on 10 classes.
  Both are tight, with `g = 5` and `g = 10`.

**Step 5: uniform coupling (N5).**
- **Bounded `L`.** Suppose `m_3(Gamma(N)) <= L` for all `N`. Since `m_0 <= m_3`, Step 2 gives
  `e(Gamma(N)) >= 1/L`. (MW2) gives `e_inf = lim_N e(Gamma(N)) >= 1/L`, and (MW1) then gives (Z) on
  Torelli-abelian representations with `eta_0 = 2 sin(pi/L)`.
- **The same bound for `d`.** (TA3) gives `d(Gamma(N)) >= 1/(3L)`, and (TA2) then gives `d_inf >= 1/(3L)`.
- **Finite image.** Let `rho` have finite image with `||rho(t_s) - 1|| < min(1/2, 2 sin(pi/L))`. By
  `mod-s2-finite-image-near-scalar-reps-are-torelli-abelian` with `lambda = 1`, `rho` is Torelli-abelian,
  so the previous bullet applies.
- **From `A_+` to `L`.** Take `b in B(Gamma')` with `b >= 0`, `3 not| chi(b)` and `chi(b) = A_+`. Send each
  orbit basis vector to the `H_1(M')`-class of its separating twists; every such class is some `v_j`, as
  in Step 1. This merge map sends `B` into `W` and preserves `chi`, and on `b >= 0` it preserves the
  `l1`-norm. So `m_3 <= A_+`.
- **The converse.** It is Step 3: `e(Gamma(N)) <= 1/g(Gamma(N))` and `d(Gamma(N)) <= 1/(3 g(Gamma(N)))`.

**Step 6: normality is used.** The `line-6` data of `mod-s2-monomial-torelli-windings-census` has
`w_2 = (0,2,2,1,0) in W` with `l1 = chi = 5`, but `e(line-6) = 1/7`. There `mult = (24, 288, 192, 72, 24)`
is not constant, and Step 1 fails. So (N1) is false without normality.
