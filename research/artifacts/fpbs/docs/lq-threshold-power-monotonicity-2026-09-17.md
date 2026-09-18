# The l^q thresholds of the two-point function are power-monotone (2026-09-17)

Author: swarm-0917-w8-w8-bs-pull (transplanter, group-rings lease on
`fpbs-two-point-lq-threshold-gap-universal`).

## 1. Setting

- `G` is a connected, locally finite, vertex-transitive graph with root `o`;
  Bernoulli bond percolation with law `P_p`.
- `tau_p(x,y) = P_p(x <-> y)`, `Z_q(p) = sum_x tau_p(o,x)^q`,
  `p_q = sup{p in [0,1] : Z_q(p) < infinity}` for `q >= 1` (as in
  `lq-two-point-walk-rate-2026-09-17.md`).
- `q_*(p) = inf{q >= 1 : Z_q(p) < infinity}` (`= infinity` if none).
- `q_0 = inf{q >= 1 : p_q > p_c}` (`= infinity` if none).

`Z_q(p)` is nondecreasing in `p` and nonincreasing in `q` (because
`tau <= 1`), so `p_q` is nondecreasing in `q`.

## 2. The thinning inequality

**Lemma 2.1.** Let `A` be an increasing event depending on finitely many
edges. For `p, g in [0,1]`, `P_{p^g}(A) >= P_p(A)^g`.

This is Grimmett, *Percolation*, 2nd ed., Theorem 2.38 (already imported in
this form by `research/artifacts/fpbs-fibre-power-improvement-2026-09-17.md`,
input (G)). A self-contained proof, used here so that nothing is imported:

*Step 1 (two-point inequality).* For `p, x, g in [0,1]`,

```text
(p + (1-p) x)^g  <=  p^g + (1 - p^g) x^g.                    (2.1)
```

Put `s = p^g in [0,1]` and `r = 1/g >= 1` (the case `g = 0` is trivial:
both sides are 1 when `x > 0` or `p > 0`, and `0^0 = 1` by convention). The
left side is `R(s) = (x + (1-x) s^r)^(1/r)`, the `l^r` norm of the vector
`(x^(1/r), (1-x)^(1/r) s)`, which is affine in `s`. A norm of an affine map
is convex, so `R` is convex on `[0,1]`. The right side `L(s) = x^g + s(1-x^g)`
is affine. `R(0) = x^(1/r) = x^g = L(0)` and `R(1) = 1 = L(1)`. A convex
function lies below the chord through its endpoint values, so `R <= L` on
`[0,1]`.

*Step 2 (induction on the number n of edges).* For `n = 0`, `P(A) in {0,1}`
and the claim is trivial. Otherwise condition on the last edge `e`:
`A_1 = {omega' : omega' + e in A}` and `A_0 = {omega' : omega' - e in A}`
are increasing events on `n - 1` edges with `A_0 ⊆ A_1` (monotonicity of
`A`). Write `a_i = P_p(A_i)`, so `a_0 <= a_1`. By induction
`P_{p^g}(A_i) >= a_i^g`. Hence

```text
P_{p^g}(A) = p^g P_{p^g}(A_1) + (1-p^g) P_{p^g}(A_0)
          >= p^g a_1^g + (1-p^g) a_0^g.
```

If `a_1 = 0` both sides vanish. Otherwise put `x = a_0/a_1 in [0,1]` and use
(2.1):

```text
p^g a_1^g + (1-p^g) a_0^g = a_1^g (p^g + (1-p^g) x^g)
                          >= a_1^g (p + (1-p) x)^g = (p a_1 + (1-p) a_0)^g = P_p(A)^g.
```

QED. (`check_thinning.py` verifies (2.1) on a grid and Lemma 2.1 by exact
enumeration on 400 random increasing events and on three connection events.)

**Corollary 2.2.** For all vertices `x, y` and `p, g in [0,1]`:
`tau_{p^g}(x,y) >= tau_p(x,y)^g`. Equivalently, for `0 < p < p' <= 1`,

```text
tau_p(x,y) <= tau_{p'}(x,y)^(log p / log p').                (2.2)
```

*Proof.* `{x <-> y}` is the increasing union over `m` of the increasing
events `{x <-> y inside B(o,m)}`, each depending on finitely many edges.
Apply Lemma 2.1 and let `m -> infinity` on both sides (monotone
convergence). For (2.2) take `g = log p'/log p in (0,1)`. QED.

## 3. Power monotonicity of the thresholds

**Theorem 3.1.** For `1 <= q < q'`: `p_(q') <= p_q^(q/q')`. Equivalently
`q -> p_q^q` is nonincreasing on `[1, infinity)`.

*Proof.* Put `g = q/q' in (0,1)`. Let `p in (p_q^g, 1]`. Then
`p^(1/g) in (p_q, 1]`, so `Z_q(p^(1/g)) = infinity`. By Corollary 2.2,
`tau_p = tau_((p^(1/g))^g) >= tau_(p^(1/g))^g` pointwise, so

```text
Z_(q')(p) = sum tau_p^(q') >= sum tau_(p^(1/g))^(g q') = Z_q(p^(1/g)) = infinity.
```

So every `p > p_q^g` has `Z_(q')(p) = infinity`, i.e. `p_(q') <= p_q^g`. QED.

**Theorem 3.2.**

1. `p_1 = p_c`. Consequently `p_q <= p_c^(1/q)` for every `q >= 1`; in
   particular `p_(2->2) <= p_2 <= sqrt(p_c)`.
2. `q -> p_q` is continuous on `[1, infinity)`.
3. `{q >= 1 : p_q > p_c} = (q_0, infinity)`, and `p_q = p_c` for
   `q in [1, q_0]` (for `q_0 < infinity`).
4. On `T_d` all of this is equality: `p_q = (d-1)^(-1/q) = p_c^(1/q)` for
   every `q >= 1`, and `q_0 = 1`.

*Proof.*

1. `Z_1(p) = chi_p = E_p|K_o|`. For `p > p_c`, `theta(p) > 0` gives
   `chi_p = infinity`, so `p_1 <= p_c`. For `p < p_c`, `chi_p < infinity`
   (Lemma 3.3 below), so `p_1 >= p_c`. The bound `p_q <= p_1^(1/q)` is Theorem 3.1 with `q = 1`
   (this half needs only `p_1 <= p_c`, no sharpness). `p_(2->2) <= p_2` is
   Lemma 4.1 of `lq-two-point-walk-rate-2026-09-17.md`.
2. Right-continuity at `q_1`: for `q > q_1`, `p_(q_1) <= p_q <= p_(q_1)^(q_1/q)`,
   and the right side tends to `p_(q_1)`. Left-continuity at `q_1 > 1`: for
   `q < q_1`, `p_(q_1)^(q_1/q) <= p_q <= p_(q_1)` (Theorem 3.1 read as
   `p_(q_1) <= p_q^(q/q_1)`), and the left side tends to `p_(q_1)`.
3. By sharpness `p_q >= p_1 = p_c` for all `q`. The set is an up-set by
   monotonicity, so it is `(q_0,infinity)` or `[q_0,infinity)`. If
   `q_0 > 1`, then `p_q = p_c` for `q < q_0` and continuity gives
   `p_(q_0) = p_c`. If `q_0 = 1`, then `p_1 = p_c`. Either way `q_0` is
   excluded.
4. `tau_p(o,x) = p^|x|` and the sphere of radius `n` has
   `d(d-1)^(n-1)` points, so `Z_q(p) < infinity` iff `(d-1)p^q < 1`. QED.

**Lemma 3.3 (subcritical susceptibility).** On a transitive `G`,
`chi_p < infinity` for every `p < p_c`.

*Imports.*

- [DT] Duminil-Copin–Tassion, arXiv:1502.03050v3, TeX source
  `sharpnessPercoIsing-H.tex`, as quoted with line numbers in the
  ESTABLISHED route `fpbs-l2-gap-class-closed-under-local-limits-proof`.
  Lines 314–322 define
  `tilde beta_c = sup{beta : varphi_beta(S) < 1 for some finite S containing 0}`
  and state verbatim "This directly implies that $\tilde{\beta_c}=\beta_c$".
  Lines 349–354 give the bond form
  `varphi_p(S) = p sum_(x in S) sum_(y notin S, {x,y} in E) P_p[0 <->_S x]`.
  So for `p < p_c` there is a finite `S` containing `o` with
  `varphi_p(S) < 1`.
- BK inequality (Grimmett, *Percolation*, 2nd ed., Section 2.3), as used in
  the ESTABLISHED `fpbs-intrinsic-l2-rate-closed-zero-set-proof`.

*Proof.* Fix `p < p_c` and such an `S`, and write `varphi = varphi_p(S)`.
For a vertex `w`, let `gamma_w` be an automorphism with `gamma_w o = w`, and
put `S_w = gamma_w S`. Then `varphi_p(S_w) = varphi` by invariance. Fix a
finite set `F`, and put `M_F = sup_w sum_(x in F) tau(w,x) <= |F|`. Let
`x in F` and `x notin S_w`. On `{w <-> x}`, take an open self-avoiding path
from `w` to `x` and its first edge `uv` with `u in S_w`, `v notin S_w`. The
part before `u` lies in `S_w` and the part after `v` is disjoint from it.
So `{w <->_(S_w) u} o {uv open} o {v <-> x}` occurs. Taking the finite-volume
approximations and applying BK gives

```text
tau(w,x) <= sum_(u in S_w, v notin S_w, uv in E) P[w <->_(S_w) u] p tau(v,x).
```

Summing over `x in F \ S_w` and adding at most `|S|` for `x in S_w`:

```text
sum_(x in F) tau(w,x) <= |S| + varphi M_F,   so   M_F <= |S| + varphi M_F.
```

Since `M_F < infinity` and `varphi < 1`, `M_F <= |S|/(1 - varphi)`. Let `F`
increase to `V`: `chi_p <= |S|/(1-varphi) < infinity`. QED.

## 4. Consequences for the hole [Q] and for the l^q family

**Corollary 4.1 (the l^q scale is one exponent).**

- [Q] (`p_c < p_q` for every `q > 2`) holds iff `q_0 <= 2`.
- `p_c < p_2` holds iff `q_0 < 2`.
- `p_c < p_q` for **some** finite `q` holds iff `q_0 < infinity`; this
  already gives `p_c < p_u` when `rho < 1`
  (`fpbs-lq-two-point-bounds-walk-rate`, item 3: `p_q <= p_u`).

So the one-parameter family of statements "[Q_q]: `p_c < p_q`" is exactly
the threshold statement `q_0 <= q`, with `q_0` a single graph invariant in
`[1, infinity]`. Every nonamenable graph where the answer is known has
`q_0 < 2` (the Hutchcroft classes, via `p_c < p_(2->2) <= p_2`), and trees
have the extreme value `q_0 = 1`.

**Corollary 4.2 (monotone index).** `Lambda(p) = q_*(p) log(1/p)` is
nondecreasing in `p` on `(0,1)`.

*Proof.* If `p < p'` and `r < q_*(p) log(1/p)/log(1/p')`, then with
`g = log p'/log p`, `g r < q_*(p)`, so `Z_(gr)(p) = infinity`; Corollary 2.2
gives `Z_r(p') >= Z_(gr)(p) = infinity`. So `q_*(p') >= q_*(p) log(1/p)/log(1/p')`.
QED. On `T_d`, `Lambda = log(d-1)` is constant.

In particular `q_*(p) >= log(1/p_c)/log(1/p)` for `p > p_c`, with equality
on trees: trees have the most summable supercritical two-point functions
for their `p_c`.

## 5. Obstruction: thinning transfer adds no slack for [Q]

A natural way to reach [Q] is to prove summability at one comfortable
parameter `p' > p_c` and transport it down to `(p_c, p')` by thinning
(2.2), which strengthens decay by the power `log p/log p' > 1`. Corollary
4.2 computes exactly what this yields: from `Z_q(p') < infinity` it gives
`q_*(p) <= q log(1/p')/log(1/p)` for `p in (p_c,p')`, hence
`q_0 <= q log(1/p')/log(1/p_c)`. So the transported statement proves [Q]
iff the input satisfies

```text
(p')^q  >=  p_c^2      (strict inequality for p_c < p_2).        (5.1)
```

**Proposition 5.1.** There exist `q >= 1` and `p' > p_c` with
`Z_q(p') < infinity` and `(p')^q > p_c^2` iff `q_0 < 2`. The non-strict
input `(p')^q >= p_c^2` implies `q_0 <= 2`. So the input the thinning
transfer needs is the conclusion itself.

*Proof.* (⇒) Given such `q, p'`, Corollary 4.2 gives, for `p in (p_c,p')`,
`q_*(p) <= q log(1/p')/log(1/p)`. For any `r > q log(1/p')/log(1/p_c)`,
pick `p > p_c` close enough to `p_c` that `q log(1/p')/log(1/p) < r`; then
`Z_r(p) < infinity`, so `p_r >= p > p_c`. Hence
`q_0 <= q log(1/p')/log(1/p_c)`, which is `< 2` under the strict input and
`<= 2` under the non-strict one. (⇐) If `q_0 < 2`, take
`q in (max(q_0,1), 2)`, so `p_q > p_c` by Theorem 3.2(3), and any
`p' in (p_c, p_q)`. Then `Z_q(p') < infinity` and
`(p')^q > p_c^q > p_c^2` because `p_c < 1` and `q < 2`. QED.

The transfer does improve the exponent, from `q` to
`q log(1/p')/log(1/p_c)`, but by a factor that tends to 1 as `p'` tends to
`p_c`. On `T_d` the bound is sharp: letting `p'` increase to
`p_q = p_c^(1/q)` gives `q_0 <= 1`.

Where the class dies: at the exponent `log p/log p'`. Thinning is an
**equality** on every tree (`tau_p = p^|x|`), so no argument that uses only
thinning-type (monotone power-coupling) comparisons between parameters can
improve the exponent. Any proof of [Q] must inject genuinely new
information at a single parameter: the value of `q_*` at `p_c + 0`. This is
the same openness step (`p_c` to `p_c + epsilon`) on which the Russo–BK,
Fourier-algebra and state-axiom approaches recorded on the hole already
die; the thinning inequality, the one parameter-comparison principle that
holds for *every* increasing event, does not cross it either.

## 6. Scope

- Everything above is unconditional for transitive graphs; nonamenability is
  used only in Corollary 4.1's last bullet (`rho < 1`).
- The collapse witness `f_p = theta(p)^2 + (1 - theta(p)^2) tau_(p_c)` of
  `fpbs-two-point-state-axioms-admit-collapse` satisfies the thinning
  inequality `f_(p^g) >= f_p^g` above `p_c` only if its free profile obeys
  roughly `theta(p)^2 >= c (p - p_c)`; the witness may choose `theta`, so
  adding thinning to the state axioms does not by itself break that
  class kill. It is a new necessary constraint on any synthetic collapse
  family, recorded here and not used.
