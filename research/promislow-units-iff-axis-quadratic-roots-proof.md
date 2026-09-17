---
rg: 2
id: promislow-units-iff-axis-quadratic-roots-proof
kind: route
title: Conjugate the axis x by a unit, use the support permutation to force triviality, and read the spectrum of an axis root from its trace
target: promislow-units-iff-axis-quadratic-roots
requires:
  - promislow-group-ring-units-are-constant-reduced-norm
  - promislow-integral-units-have-monomial-definite-line-shadows
---

Notation is as in `promislow-units-iff-axis-quadratic-roots`. `R` is a
commutative domain, `L = <x, y, z> = Z^3`, `P/L = K4` with coset
representatives `1, a, b, ab`, and `c = x + x^-1`, `q(T) = T^2 - cT + 1`.

**Step 0 (facts about P).**
- *Actions.* From `a^-1 b^2 a = b^-2` and `b^-1 a^2 b = a^-2`, conjugation by `a`
  or `b` inverts `y` or `x` respectively. Since the actions are involutions,
  `a b^2 = b^-2 a` and `a^2 b = b a^-2`. Hence
  `b a b a . a b a b = b a (b a^2 b) a b = b a b^2 a^-2 a b = b (a b^2) a^-1 b = b b^-2 a a^-1 b = 1`,
  so `b z b^-1 = baba = z^-1`. The rest of the table in
  `promislow-group-ring-units-are-constant-reduced-norm` follows the same way.
  In particular `c = x + x^-1` and `y + y^-1` are central in `R[P]`.
- *Centralisers.* Write `p = l k` with `l in L` and `k in {1, a, b, ab}`, and
  let `N != 0`. Then `p x^N p^-1 = k x^N k^-1 = x^(+-N)`, with the sign `+`
  exactly for `k in {1, a}`. Since `x` has infinite order,
  `C_P(x^N) = L u La`. Likewise `C_P(y^N) = L u Lb`, so
  `C_P(x^N) cap C_P(y^M) = L` for all `N, M != 0`.
- *The automorphism psi.* Put `psi(a) = b`, `psi(b) = ab`.
  - First relator: `psi(b^-1 a^2 b a^2) = b^-1 a^-1 b^2 a b b^2 = b^-1 b^-2 b b^2 = 1`,
    using `a^-1 b^2 a = b^-2`.
  - Second relator: `psi(a^-1 b^2 a b^2) = b^-1 z b z = z^-1 z = 1`.

  So `psi` is an endomorphism of `P`. It is onto because `b = psi(a)` and
  `a = psi(b) psi(a)^-1`. `P` is finitely generated and virtually `Z^3`, hence
  residually finite, hence Hopfian (Mal'cev), so `psi` is an automorphism. Its values on the axes:
  - `psi(x) = b^2 = y`;
  - `psi(y) = (ab)^2 = z`;
  - `psi(z) = b ab b ab = b (a b^2) a b = b b^-2 a a b = b^-1 a^2 b = x^-1`.

  All of this is also checked mechanically in `axis_quadratic_calibration.py`
  (log: `psi relators trivial: True True`, `psi(z) ... (=X)`,
  `psi onto ... True`). `psi` extends to a ring automorphism of `R[P]` that
  maps trivial units to trivial units.

**Step 1 (axis roots are units).** If `q(v) = 0`, then, since `c` is central,
`v (c - v) = (c - v) v = cv - v^2 = 1`. So `v` is a unit with `v^-1 = c - v`.

**Step 2 (trivial axis roots).** Let `v = lambda g` with `lambda != 0` and
`g in P`. Then

    q(v) = lambda^2 g^2 - lambda xg - lambda x^-1 g + 1.

Here `xg != x^-1 g`. So the coefficient of `xg` in `q(v)` is
`-lambda + lambda^2 [g^2 = xg] + [xg = 1]`, where `[.]` is 1 or 0. The two
brackets cannot both be 1: that would need `g = x` and `g = x^-1` at once. If
neither is 1, the coefficient is `-lambda != 0`. So `q(v) = 0` forces
`g = x` or `g = x^-1`.
- If `g = x`: `q(v) = (lambda^2 - lambda) x^2 + (1 - lambda)`, so `lambda = 1`.
- If `g = x^-1`: `q(v) = (lambda^2 - lambda) x^-2 + (1 - lambda)`, so
  `lambda = 1`.

Both `x` and `x^-1` are roots. So the trivial axis roots are exactly `x` and
`x^-1`. Applying `psi`, the trivial roots of `T^2 - (y + y^-1) T + 1` are
exactly `y` and `y^-1`.

**Step 3 ((b) => (a)).** An axis root other than `x^(+-1)` is a unit by
Step 1, and it is nontrivial by Step 2.

**Step 4 (support lemma).** *Let `u` be a unit of `R[P]` with
`u x u^-1 = g in {x, x^-1}` and `u y u^-1 = h in {y, y^-1}`. Then `u` is
trivial.*

Let `S = supp(u)`, a finite nonempty set.
- *A permutation of S.* From `ux = gu`, and since multiplication by a group
  element permutes supports, `Sx = gS`. So `sigma(s) = g^-1 s x` maps `S` into
  `S`. It is injective, so it is a permutation of `S`.
- *Where S lies.* With `N = |S|!`, `sigma^N = id`, that is
  `s x^N s^-1 = g^N` for every `s in S`. For `s, t in S` this gives
  `t^-1 s in C_P(x^N)`. The same argument with `y` gives
  `t^-1 s in C_P(y^N)`. By Step 0, `t^-1 s in L`. Fix `s_0 in S`. Then
  `S ⊂ s_0 L`, so `u = s_0 f` with `f in R[L]`.
- *f is a unit.* Let `w = u^-1 s_0` and write `w = sum_k w_k k` with
  `w_k in R[L]` (`k in {1, a, b, ab}`). From `u u^-1 = 1` we get `f w = 1`,
  so `sum_k (f w_k) k = 1`. Each `f w_k` lies in `R[L]`, and the cosets `Lk`
  are disjoint, so `f w_1 = 1`.
- *Conclusion.* `R[L]` is a Laurent polynomial ring over the domain `R`, so
  its units are `lambda l` with `lambda in R^x`, `l in L`. Hence
  `u = lambda s_0 l` is trivial.

**Step 5 ((a) => (b)).** Let `u` be a nontrivial unit.
- *Two candidate roots.* Put `v_x = u x u^-1`. Since `c` is central,
  `q(v_x) = u q(x) u^-1 = 0`, so `v_x` is an axis root. Put
  `v_y = u y u^-1`. It is a root of `T^2 - (y + y^-1) T + 1`, because
  `y + y^-1` is central. So `psi^-1(v_y)` is a root of
  `T^2 - (x + x^-1) T + 1`, that is, an axis root.
- *One of them is nontrivial.* By Step 4, `v_x not in {x, x^-1}` or
  `v_y not in {y, y^-1}`. In the first case `v_x` is a nontrivial axis root.
  In the second case `v_y` is nontrivial by Step 2 transported by `psi`, so
  `psi^-1(v_y)` is a nontrivial axis root.

This proves item 1.

**Step 6 (item 2).**
- *Unit form.* If `q(v) = 0`, then `v^-1 = c - v` gives `v + v^-1 = c`.
  Conversely, if `v` is a unit with `v + v^-1 = c`, multiplying by `v` gives
  `v^2 + 1 = cv`.
- *The form in n.* Put `n = v - x^-1`. Then

      n^2 - x n + n x^-1 = (v^2 - v x^-1 - x^-1 v + x^-2) - (x v - 1) + (v x^-1 - x^-2)
                         = v^2 - (x + x^-1) v + 1 = q(v).

  Here `x^-1 v + x v = cv` holds by definition of `c`. So `q(v) = 0` iff
  `n^2 = x n - n x^-1`. The two trivial roots give `n = 0` (`v = x^-1`) and
  `n = x - x^-1` (`v = x`).
- *Intertwiners.* If `q(v) = 0`, then `v^2 = cv - 1`, so
  - `(v - x^-1) v = cv - 1 - x^-1 v = xv - 1 = x (v - x^-1)`;
  - `(v - x) v = cv - 1 - xv = x^-1 v - 1 = x^-1 (v - x)`.
- *The form in K.* For `K = 2v - c`,
  `K^2 = 4v^2 - 4cv + c^2 = 4 q(v) + (c^2 - 4)`, and
  `c^2 - 4 = x^2 - 2 + x^-2 = (x - x^-1)^2`. If `2 in R^x`, then
  `v -> 2v - c` is a bijection from axis roots to square roots of
  `(x - x^-1)^2`, with inverse `K -> (K + c)/2`. It sends `x` and `x^-1` to
  `x - x^-1` and `-(x - x^-1)`.

**Step 7 (item 3: the spectrum of an axis root).** Let `R` be a domain in which
`2 != 0`, and let `F = Frac(R[L])`. Let `M(v)` be the matrix over `R[L]` of
either of these maps on the free `R[L]`-module `R[P]` with basis
`1, a, b, ab`:
- left multiplication `w -> v w`, with `R[L]` acting on the right, which gives
  a ring homomorphism `rho`;
- right multiplication `w -> w v`, with `R[L]` acting on the left, which gives
  a ring anti-homomorphism (the `Nrd` matrix of
  `promislow-group-ring-units-are-constant-reduced-norm`).

In both cases `M(v^2) = M(v)^2` and `M(1) = I`. Since `c` is central,
`k c = c k`, so `M(c) = cI`. Hence `M(v)^2 - c M(v) + I = 0` over `F`.

*Eigenvalues.* The polynomial `(T - x)(T - x^-1)` has distinct roots in `F`,
so `M(v)` is diagonalisable over `F`. Its eigenvalues are `x`, with some
multiplicity `m`, and `x^-1`, with multiplicity `4 - m`. So
`tr M(v) = m x + (4 - m) x^-1`.

*The trace is K4-invariant.* For `g in P` the `(k, k)` entry of `M(g)` is
nonzero exactly when `gk in kL` (left case) or `kg in Lk` (right case). Since
`L` is normal, both happen exactly when `g in L`, and then the entry is
`k^-1 g k` or `k g k^-1`. So

    tr M(v) = sum_{g in L} v_g sum_{k in {1,a,b,ab}} k^(-+1) g k^(+-1).

Conjugating by `b` permutes the inner sum modulo `L`, and conjugation by `L`
fixes `L`, so `tr M(v)` is `K4`-invariant. Conjugation by `b` inverts `x`,
which gives `m x + (4 - m) x^-1 = m x^-1 + (4 - m) x`, i.e.
`(2m - 4)(x - x^-1) = 0` in the domain `R[L]`.

*Conclusion.* `2m - 4` lies in `{0, +-2, +-4}` and `2 != 0`, so `m = 2`. The
characteristic polynomial of `M(v)` is therefore `(T - x)^2 (T - x^-1)^2`,
equal to `(T^2 - cT + 1)^2`, in `F[T]`, hence in `R[L][T]`. This is the
characteristic polynomial of `M(x)` (`diag(x, x, x^-1, x^-1)` in the left
case). In particular `det M(v) = 1`, so `Nrd(v) = 1`.

**Step 8 (the invariants).** Now take `R ⊂ C`. For a character
`xi: L -> C^x`, specialise `rho` to `V(xi) = rho_xi(v)` in `M_4(C)`.
- *Eigenvalues.* Specialisation commutes with taking the characteristic
  polynomial, so the characteristic polynomial of `V(xi)` is
  `(T - t)^2 (T - t^-1)^2` with `t = xi(x)`. This gives the first two bullets.
- *Mahler measure and spectral radius.* If `xi` is unitary then `|t| = 1`.
  Every fibre then has spectral radius 1, and
  `m(v) = int_{T^3} sum_i log+ |lambda_i(xi)| d xi = 0`. By Jensen's formula
  this is the Mahler measure of the monic polynomial `det(T - rho(v))`.
- *The trace formula.* For `g in P` and unitary `xi`, `rho_xi(g)` is a monomial
  matrix with unimodular entries, hence unitary, and
  `rho_xi(g^-1) = rho_xi(g)^*`. By Step 7, `tr rho_xi(g) = 0` unless
  `g in L`, and then it is `sum_k xi(k^-1 g k)`. Integrating over `T^3` gives
  `(1/4) int tr rho_xi(g) d xi = [g = 1] = tau(g)`. So
  `rho = int^oplus rho_xi` is a trace-preserving `*`-homomorphism
  `C[P] -> M_4(L^inf(T^3))`, with trace `(1/4) int tr`. It extends to a
  trace-preserving normal embedding of the group von Neumann algebra `L(P)`.
- *Trace sequence.* For `k != 0`,
  `tau(v^k) = (1/4) int tr V(xi)^k d xi = (1/4) int 2 (t^k + t^-k) d xi = 0`,
  because `int xi(x^(+-k)) d xi = 0`. Negative powers are covered as well,
  since `v^-1 = c - v` has the same eigenvalues.
- *Fuglede--Kadison determinant.* Using the trace-preserving embedding,
  `log Delta(v) = (1/4) int log |det V(xi)| d xi = 0`.
- *Brown measure.* The same embedding gives
  `log Delta(v - lambda) = int (1/4) sum_i log |lambda_i(xi) - lambda| d xi`
  for every `lambda in C`. The Brown measure is `(1/2 pi)` times the Laplacian
  of this in `lambda`, so it is `int (1/4) sum_i delta_(lambda_i(xi)) d xi`,
  which equals `(1/2)(t_* Haar + (t^-1)_* Haar)`, that is, Haar measure on the
  unit circle. For `x` the computation is the same.

*Why these invariants cannot detect a nontrivial unit.* If `u` is a nontrivial
unit, Step 5 gives a nontrivial axis root `v_x = u x u^-1` or
`psi^-1(u y u^-1)`. All of the invariants above coincide for it and for `x`.
For `v_x` the reason is simply that `u -> u x u^-1` preserves them. For
`psi^-1(u y u^-1)` it is Steps 7 and 8.

**Step 9 (item 4: shadows over Z).** Let `v in Z[P]` be an axis root. It is a
unit (Step 1). By item 1 of
`promislow-integral-units-have-monomial-definite-line-shadows`, `X = phi_i(v)`
is `+-t^m` or `+-t^m u` in `D(Z)`, for each shadow `phi_i`.
- *Shadows B and C.* Both send `x` to `-1`, so `phi_i(c) = -2` and
  `X^2 + 2X + 1 = 0`.
  - If `X = +-t^m u`, then `X^2 = t^m t^-m u^2 = -1`, and
    `X^2 + 2X + 1 = 2X != 0`.
  - If `X = +-t^m`, then `(X + 1)^2 = 0` in the domain `Z[t^(+-1)]`, so
    `X = -1`.

  Hence `phi_B(v) = phi_C(v) = -1 = phi_i(x^(+-1))`, and both `v - x` and
  `v - x^-1` lie in `I_B cap I_C`.
- *Shadow A.* It sends `x` to `t^2`, so `phi_A(c) = t^2 + t^-2`. This is
  central in `D(Z)`, because `u t^2 = t^-2 u`.
  - If `X = +-t^m u`, then `X^2 + 1 = 0`, so `q(X) = -(t^2 + t^-2) X != 0`.
  - If `X = +-t^m`, then `X` lies in the commutative domain `Z[t^(+-1)]`,
    where `q(T) = (T - t^2)(T - t^-2)`. So `X = t^2` or `X = t^-2`.

  So `v - x in I_A` or `v - x^-1 in I_A`.
- *Conclusion.* Combining the two bullets, `v - x in I_A cap I_B cap I_C` or
  `v - x^-1 in I_A cap I_B cap I_C`. Replacing `v` by `c - v` swaps
  `phi_A(v) = t^-2` with `t^2`. This proves item 4.

**Calibration.** The artifacts check Steps 0, 5 and 8 on Gardam's unit
`alpha` over `Z[zeta_8]`, where nontrivial units exist, so the reduction must
produce nontrivial axis roots there. It does: `alpha x alpha^-1`,
`alpha y alpha^-1` and `alpha z alpha^-1` are nontrivial roots of their
quadratics, and `alpha x alpha^-1` has Mahler measure 0 (to `1e-13`), while
`alpha` has about `1.41`. Step 9 is the only step that uses `R = Z`. It fails
over `Z[zeta_8]` exactly where item 5 of
`promislow-integral-units-have-monomial-definite-line-shadows` says shadows
stop being monomial.
