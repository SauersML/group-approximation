---
rg: 2
id: finite-simple-rr0-sr1-via-weak-cancellation
kind: route
title: Weak cancellation makes a finite simple real rank zero algebra stably finite, cancellative, and of stable rank one
target: finite-simple-rr0-algebras-have-stable-rank-one
requires: [finite-simple-rr0-algebras-have-weak-cancellation]
---

Together with `finite-simple-rr0-weak-cancellation-via-stable-rank-one`, this
route makes the two claims equivalent.  It formalizes the parenthetical in
Schafhauser--Tikuisis--White (arXiv:2506.10902, discussion before Problem LX,
read 2026-09-16): for separative unital real rank zero algebras finiteness gives
stable finiteness (AGOP Theorem 7.6), "and in the simple case, this also implies
stable rank one".  The argument below is self-contained and does not use AGOP.

**Setting.**  `C` is a unital simple C\*-algebra of real rank zero with finite
unit.  `V(C)` is the Murray--von Neumann monoid of projections in `M_inf(C)`,
and `u = [1_C]`.  Weak cancellation is read as in the target claim and in its
use in `stw29-via-finite-simple-rr0-weak-cancellation`, for projections over
`C`: if `x, y, z` are in `V(C)`, `x, y != 0` and `x + z = y + z`, then `x = y`.
By simplicity every nonzero projection over `C` is full, so no fullness
hypothesis remains.

Two elementary facts are used.

* (E1) If projections `e, f` in `M_n(C)` are equivalent in some `M_m(C)`,
  `m >= n`, they are equivalent in `M_n(C)`.  A partial isometry `w` with
  `w*w = e` and `ww* = f` satisfies `w = f w e`, so its entries lie in the
  `n x n` corner.
* (E2) Real rank zero for unital `C` means, by definition, that invertible
  self-adjoint elements are dense in the self-adjoint part.  Stable rank one
  means, by definition (Rieffel), that left invertible elements are dense.  So
  density of invertible elements gives `tsr(C) = 1`.

**Step 1: stable finiteness.**  Suppose a projection `p` in `M_m(C)` is
infinite: `[p] = [p] + s` with `s != 0`.  Adding `[1_m - p]` gives
`m u = m u + s`.  If `m = 1` this reads `u + s = u`.  If `m >= 2` write it as
`(u + s) + (m - 1) u = u + (m - 1) u`, and weak cancellation (both `u + s` and
`u` are nonzero) again gives `u + s = u`.  Realize `s` by a nonzero projection
`e` in some `M_j(C)`.  By (E1) there is `W` in `M_(1+j)(C)` with
`W*W = 1_C direct_sum e` and `WW* = 1_C direct_sum 0`.  Put
`w = W (1_C direct_sum 0)`.  Then `w*w = 1_C direct_sum 0`, and `ww*` is dominated
by `WW* = 1_C direct_sum 0`, so `w` lies in the corner
`(1_C direct_sum 0) M_(1+j)(C) (1_C direct_sum 0)`, which is `C`.  In `C`,
`w` is an isometry, and `1_C - ww*` corresponds to `W (0 direct_sum e) W*`,
which is a projection equivalent to `e != 0`.  So `w` is a non-unitary isometry
in `C`, contradicting finiteness of `1_C`.  Hence every projection over `C` is
finite, i.e. `x + s = x` implies `s = 0` in `V(C)`.

**Step 2: cancellation in `V(C)`.**  Let `x + z = y + z`.  If `x, y != 0`,
weak cancellation gives `x = y`.  If `x = 0`, then `z = z + y`, so `y = 0` by
Step 1; symmetrically if `y = 0`.

**Step 3: internal cancellation.**  Let `e, f` be projections in `C` with
`e ~ f`.  Then `[1_C - e] + [e] = u = [1_C - f] + [f]` with `[e] = [f]`, so
`[1_C - e] = [1_C - f]` by Step 2, and `1_C - e ~ 1_C - f` in `C` by (E1).

**Step 4: invertible elements are dense.**  Let `x` be in `C` and `eps > 0`.
Put `a = x*x` and choose `eta > 0` with `3 eta < eps^2`.  By (E2) pick an
invertible self-adjoint `h` with `||h - (a - 2 eta)|| < eta`.  Since `0` is
not in the spectrum of `h`, `e = chi_(0,inf)(h)` is a projection in `C`
commuting with `h`, with `h e >= 0` and `h (1 - e) <= 0`.  Then

```text
e a e = 2 eta e + e h e + e (a - 2 eta - h) e >= 2 eta e - eta e = eta e,
(1-e) a (1-e) = 2 eta (1-e) + (1-e) h (1-e) + (1-e)(a - 2 eta - h)(1-e)
             <= 2 eta (1-e) + eta (1-e) = 3 eta (1-e).
```

So `||x - x e||^2 = ||(1-e) a (1-e)|| <= 3 eta < eps^2`.  Put `y = x e`.  In
the unital corner `eCe`, `y*y = e a e >= eta e` is invertible.  Let `t` be its
positive square root in `eCe`, `t^(-1)` its inverse there, and `v = y t^(-1)`.
Then `v*v = t^(-1) t^2 t^(-1) = e`, `v = v e`, and `f = v v*` satisfies
`v = f v`.  By Step 3 there is `s` in `C` with `s*s = 1 - e` and
`s s* = 1 - f`, so `s = (1 - f) s (1 - e)`.  (If `e = 0` then `v = 0`, `f = 0`,
and `s = 1` works; if `e = 1`, Step 3 forces `f = 1` and `s = 0`.)  The
cross terms vanish: `v*s = v* f (1-f) s = 0`, `v s* = v e (1-e) s* = 0`.  Hence
`U = v + s` is a unitary, since `U*U = e + (1 - e)` and `UU* = f + (1 - f)`.
For `delta > 0` the element `T = t + delta (1 - e)` is invertible in `C`, being
the orthogonal sum of invertible elements of `eCe` and `(1-e)C(1-e)`.  Using
`v t = y`, `v (1-e) = 0`, `s t = s (1-e) e t = 0` and `s (1-e) = s`,

```text
U T = v t + delta v (1-e) + s t + delta s (1-e) = y + delta s .
```

So `y + delta s` is invertible and
`||x - (y + delta s)|| <= ||x - y|| + delta < eps + delta`.  As `eps` and
`delta` are arbitrary, invertible elements are dense in `C`, and `tsr(C) = 1`
by (E2).

**Where the hypotheses enter.**  Finiteness of `1_C` is used only in Step 1.
Simplicity is used only to make every nonzero projection full, so that weak
cancellation applies in Steps 1 and 2.  Real rank zero is used only in Step 4.
Steps 3 and 4 show more generally that a unital real rank zero algebra whose
projections satisfy internal cancellation (`e ~ f` implies `1 - e ~ 1 - f`) has
stable rank one.
