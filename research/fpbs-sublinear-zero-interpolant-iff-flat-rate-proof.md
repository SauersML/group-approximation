---
rg: 2
id: fpbs-sublinear-zero-interpolant-iff-flat-rate-proof
kind: route
title: Divide out the o(n) zeros, bound the n-th root of the zero-free quotient by the mean-value property, and propagate |g|=rho from the interval to p_+ through g times its Schwarz reflection
target: fpbs-sublinear-zero-interpolant-iff-flat-rate
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs-sublinear-zero-flat-rate-2026-09-18.md
---

Complete written proof. Notation is that of the target.

**Imports.**

- (K) Kesten: `rho<1`, and `r_(2m)=P(X_(2m)=o)` has `r_(2m)^(1/(2m)) -> rho`
  (Trans. AMS 92 (1959); Woess, *Random walks on infinite graphs and groups*,
  Sections 1 and 12). The self-contained Fekete-plus-trace argument is in
  `fpbs-zero-free-flat-rate-vitali-proof`, import (K).
- (S) `fpbs-critical-walk-correlation`: `a_n(p_c) <= rho^n`. It is used only
  in (C2).
- Harris-FKG; Newman-Schulman (0, 1 or infinitely many infinite clusters);
  Montel; the identity theorem; the mean-value property of harmonic functions;
  and the circle average `(1/2pi) int log|z + r e^(it) - zeta| dt = log max(r, |z-zeta|)`.

**Step 0: lower bound and supermultiplicativity.** For `0<p<=1` and every
`R>=1`, `a_(n,R)(p) >= r_n` if `n` is even and `a_(n,R)(p) >= p r_(n-1)` if
`n` is odd. (On `{X_(n-1)=o}` the edge `o X_n` lies in `B_1`.) So
`liminf a_n(p)^(1/n) >= rho` by (K), uniformly on compacts of `(0,1]`, and
`a_n(p)>0`.

Next, `a_(n+m) >= a_n a_m`. The events `{o<->x}` and `{x<->y}` are increasing,
so Harris-FKG gives `tau(o,y) >= tau(o,x) tau(x,y)`. By left invariance,
`tau(x,y) = tau(o, x^(-1) y)`. The increment `X_n^(-1) X_(n+m)` is independent
of `X_n` and has the law of `X_m`. Averaging gives the bound. By Fekete,
`lambda(p) = lim a_n^(1/n) = sup_n a_n^(1/n)`. In particular
`a_n(p) <= lambda(p)^n` for all `n`.

**1 <=> 2.** Given 1, Fekete gives 2. Given 2, `lambda(p_+) <= rho`, and Step 0
gives `>=`.

**2 => 3.** Take `U = C`, any `I`, `S = N` and `F_n = rho^n`. Alternatively take
`F_n = a_(n,1)`. It is `r_n` plus
`sum_(x ~ o) P(X_n = x) P_z(o <-> x in B_1)`, a polynomial of degree at most
`|E(B_1)|` with bounded coefficients. It has (G) and at most `|E(B_1)|` zeros
unless it vanishes identically, which Step 0 excludes. It has (E) on
`I` in `(0,p_c]` by Step 0 and (S), and it has (P) because
`a_n(p_+) <= rho^n <= e^(o(n)) a_(n,1)(p_+)` by 2 and Step 0.

**3 => 2.**

*Choosing the domains.* Fix a compact nondegenerate interval `J` in `I` and a
path `gamma` in `U` from a point of `J` to `p_+`. Then
`K_0 = J union gamma union conj(gamma)` is compact, connected, symmetric, and
lies in `U`.

- Let `K_1` be `K_0` together with the bounded components of `C - K_0`. Then
  `K_1` lies in `U`: `U` is simply connected, so `C - U` has no bounded
  component, and a bounded component of `C - K_0` containing a point outside
  `U` would separate that point from infinity inside `C - U`.
- Let `delta = dist(K_1, C - U) > 0`, and for `s>0` let `N_s` be the open
  `s`-neighbourhood of `K_1`. The fill of a set means the set together with
  the bounded components of its complement.
- Put `D = fill(N_(delta/3))` and `D_1 = fill(N_(2 delta/3))`. The same
  argument shows that both are simply connected domains, `D` symmetric and
  connected, with `closure(D) in D_1` and `closure(D_1)` a compact subset of
  `U`.
- Put `r = min(1/2, dist(closure(D), C - D_1)/2) > 0` and
  `d = max(1, diam D_1)`.

*Dividing out zeros.* For `n` in `S`, `F_n` is not identically zero, by (E).
Let `zeta_1,...,zeta_m` (`m = m_n`) be its zeros in `D_1` with multiplicity.
By (Z) for the compact set `closure(D_1)`, `m_n = o(n)`. Put
`Q_n = prod_j (z - zeta_j)` and `G_n = F_n/Q_n`. `G_n` is analytic and zero-free
on the simply connected `D_1`, so `G_n = e^(L_n)` there; put
`h_n = e^(L_n/n)`, so that `|h_n| = |G_n|^(1/n)`.

*Upper bound.* Let `z` be in `closure(D)`. The closed disc of radius `r`
about `z` lies in `D_1`, where `log|G_n|` is harmonic. By the mean value
property, (G) for the compact set `closure(D_1)`, and the circle average,

    (1/n) log|G_n(z)| = avg_(|w-z|=r) [ (1/n) log|F_n(w)| - (1/n) sum_j log|w - zeta_j| ]
                     <= M + (m_n/n) log(1/r),

with `M = M_(closure(D_1))`. So `|h_n| <= e^(M+1)` on `D` for large `n` in
`S`.

*Limits.* By Montel, every infinite subset of `S` has an infinite subset `S'`
along which `h_n -> g` locally uniformly on `D`, with `g` analytic.

- *Pointwise on J.* For `x` in `J`, `|Q_n(x)| <= d^(m_n)`, so
  `|h_n(x)| >= |F_n(x)|^(1/n) d^(-m_n/n)`. This tends to `rho` uniformly on
  `J` by (E). Hence `|g| >= rho > 0` on `J`, and
  `log|h_n| -> log|g|` uniformly on `J`.
- *Integrated on J.* Let `C_J = sup_(c real) (- int_J log|x-c| dx)`, which is
  finite. For every complex `zeta`, `|x-zeta| >= |x - Re zeta|`, so
  `int_J log|x-zeta| dx >= -C_J`. Hence

      int_J log|h_n| dx = int_J (1/n) log|F_n| dx - (1/n) sum_j int_J log|x-zeta_j| dx
                        <= int_J (1/n) log|F_n| dx + (m_n/n) C_J  ->  |J| log rho.

  So `int_J log|g| <= |J| log rho`. Together with `log|g| >= log rho` and
  continuity, this gives `|g| = rho` on `J`.
- *Reflection.* Put `g*(z) = conj(g(conj z))`. It is analytic on `D`, since
  `D` is symmetric. `phi = g g*` is analytic on the connected `D`, and
  `phi(x) = |g(x)|^2` for real `x` in `D`. So `phi = rho^2` on `J`, hence on
  `D` by the identity theorem. Therefore `|g(p_+)| = rho`.

*At p_+.* By (P), `a_n(p_+) <= e^(o(n)) |Q_n(p_+)| |h_n(p_+)|^n`
`<= e^(o(n)) d^(m_n) |h_n(p_+)|^n`. Along `S'` this gives
`limsup a_n(p_+)^(1/n) <= |g(p_+)| = rho`. Every infinite subset of `S`
contains such an `S'`, so `limsup_(n in S) a_n(p_+)^(1/n) <= rho`. The full
limit `lambda(p_+)` exists (Step 0), so `lambda(p_+) <= rho`, and Fekete gives 2.

**Consequences for uniqueness.** Let `p <= p_+`. By monotonicity in the
parameter and 2, `a_n(p) <= a_n(p_+) <= rho^n -> 0`. If `P_p` had a unique
infinite cluster, Harris-FKG would give
`a_n(p) >= theta(p)^2 > 0` for all `n`, a contradiction. So `p_u >= p_+ > p_c`.
For `p` in `(p_c,p_+]`, `theta(p)>0` and there is no unique infinite cluster,
so by Newman-Schulman there are infinitely many.

**(C2).** Under (ZG) on symmetric `U`, with the weakenings stated, let `p_+`
be a real point of `U` in `(p_c,1)`, and `I` a real interval of `U` in
`(0,p_c]`. `a_(n,R)` increases to `a_n` as `R -> infinity`, so for each `n`
some `R_n >= n` has `a_(n,R_n)(p_+) >= a_n(p_+)/2`. Put `F_n = a_(n,R_n)`.

- (P) holds by the choice of `R_n`.
- (G) and (Z) hold by hypothesis.
- (E): on `I`, `r_n` or `p r_(n-1)` is at most `a_(n,R)(p)`, which is at most
  `a_n(p_c) <= rho^n` by (S), for every `R`.

**(C3).** Write `I = (c-s, c+s)`. Let `T_n` be the Chebyshev polynomial,
`eta_n = n^(-1/2)`, and `F_n(z) = rho^n T_n((z-c)/s - i eta_n)`.

- *Zeros.* They are `c + s(cos((2k-1)pi/(2n)) + i eta_n)`, `k=1..n`, and lie in
  a fixed compact neighbourhood of `closure(I)`.
- *(G).* `|T_n(w)| <= (|w| + (|w|^2+1)^(1/2))^n`.
- *(E).* For `x` in a compact of `(-1,1)`, write
  `x - i eta_n = cos(t + i sigma)` with `t` in `(0,pi)`. Then
  `|sigma| ~ eta_n / sin t` uniformly, and
  `|T_n|^2 = cos^2(n t) + sinh^2(n sigma)`. This lies between
  `sinh^2(n|sigma|)` and `cosh^2(n|sigma|)`. Since `n eta_n -> infinity` and
  `eta_n -> 0`, `|T_n|^(1/n) -> 1` uniformly.
- *At p_+.* For real `p_+` with `w = (p_+-c)/s`, `|w| > 1`,
  `|T_n(w - i eta_n)|^(1/n) -> |w| + (w^2-1)^(1/2) = e^(g(p_+)) > 1`.

**(C4).** Suppose `lambda(p_+) > rho`, and fix a family with (E), (P) and (G)
along all `n`. Take an exhaustion `K_1 in K_2 in ...` of `U` by compacts, with
each compact of `U` inside some `K_j`. Suppose that for every `j`,
`liminf_n m_n(K_j)/n = 0`. Choose `n_1 < n_2 < ...` with
`m_(n_j)(K_j) <= n_j/j`. Then every compact `K` has `m_(n_j)(K) = o(n_j)`, so
3 holds along `S = {n_j}`, contradicting `lambda(p_+) > rho`. So some `K_j`
has `liminf m_n(K_j)/n > 0`. QED.
