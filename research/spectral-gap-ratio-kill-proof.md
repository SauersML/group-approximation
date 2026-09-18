---
rg: 2
id: spectral-gap-ratio-kill-proof
kind: route
title: Prove the spectral-gap ratio gate from AKKSTV rounding, and its sharpness and the completeness-1/4 expander hardness by a degree-product shift overlay
target: spectral-gap-ratio-reductions-cannot-prove-ugc
requires: [unique-games-on-expanding-constraint-graphs-are-easy, unique-games-hard-at-completeness-one-half]
artifacts:
  - experiments/ugc-calibration-2026-09-17/check_shift_overlay.py
---

Notation is that of the target claim. For a function `f : V → R` put
`Q_A(f) = sum_(edges e = {u,v}, u != v) w_e (f_u − f_v)^2` (loops contribute
nothing) and `||f||_D^2 = sum_u deg(u) f_u^2`.

## (0) Rayleigh form of λ_2

`D − A` has quadratic form `Q_A`, because a loop of weight `w` adds `w` to both
`A_uu` and `deg(u)`. Substituting `g = D^(1/2) f` in the normalized Laplacian
`I − D^(−1/2) A D^(−1/2)`, whose bottom eigenvector is `D^(1/2) 1` with
eigenvalue `0`, Courant--Fischer gives

```text
λ_2 = min { Q_A(f) / ||f||_D^2 : f != 0, sum_u deg(u) f_u = 0 }.
```

## (1) Proof of (K1)

`X(s)` exists: `log(x)/x → 0`. Let `x` be an input and `U = f(x)`.

*YES.* `U` is loop-free and regular with `λ = λ_2(U) > 0` and
`λ >= X(s)(1 − opt(U))`. Put `η = λ / X(s) > 0`. Then `opt(U) >= 1 − η` and
`λ = X(s) η >= 3η >= eη`. The instance is a finite constraint multiset, so it is
a unique game in the paper's sense, with `E_((u,v) in E)` uniform over the
multiset. For a loop-free `d`-regular multigraph, `E_(e) ||z_u − z_v||^2 =
Q(z)/W` with `vol = dn = 2W`, and `E_(u,v in V) ||z_u − z_v||^2 =
(2/n) sum_u ||z_u − z̄||^2`. Their ratio is exactly the Rayleigh quotient of (0).
So characterization (7) quoted in the citation route is the λ_2 used here, and
the import applies. It returns a labeling of value at least

```text
1 − C_A (η/λ) log(λ/η) = 1 − C_A log(X(s))/X(s) > s.
```

*NO.* Every labeling has value at most `opt(U) <= s`.

So accepting iff `val(AKKSTV(U)) > s` decides `L`. Computing `U`, running
`AKKSTV` and evaluating the returned labeling take polynomial time, and `s` and
`X(s)` are constants. Hence `L in P`. The hypotheses "loop-free" and "regular"
are used only to match the quoted proof (characterization (7)).

## (2) The overlay: values

Let `U` be as in the setting and `c > 0`. For `u != v`, put
`β_uv = c deg(u) deg(v)/vol`, and add the `k` constraints `x_v = x_u a`
(`a in Γ`), each of weight `β_uv / k`. Right multiplication by `a` is a
permutation of `Γ`, so `O_c U` is a unique game over `Γ` on the same vertices.

*Total overlay weight.*
`Ω = sum_(u<v) β_uv = c (vol^2 − sum_u deg(u)^2)/(2 vol)`. This is `> 0` since
`n >= 2` and all degrees are positive. It is `<= c vol/2 <= c W`, since a
non-loop edge adds `2w` to `vol` and a loop adds `w`.

*Value identity.* Fix a labeling `x`. For each pair `u != v`, exactly one
`a in Γ` satisfies `x_v = x_u a`, namely `a = x_u^(−1) x_v`. So the satisfied
overlay weight is `sum_(u<v) β_uv/k = Ω/k`, and

```text
val_(O_c U)(x) = (W val_U(x) + Ω/k) / (W + Ω).
```

*Bounds on opt.* The right side is a convex combination of `val_U(x)` and `1/k`,
so it is at most `max(val_U(x), 1/k)`. It is at least `W val_U(x)/(W + Ω)`,
which is at least `val_U(x)/(1+c)`. Maximizing over `x` gives

```text
opt(U)/(1+c) <= opt(O_c U) <= max(opt(U), 1/k).
```

*Loop-free games.* If `U` is loop-free, a uniformly random labeling satisfies
each constraint `x_v = π(x_u)` with `u != v` with probability `1/k`. So
`opt(U) >= 1/k`, and then `opt(O_c U) <= opt(U)`. With loops this can fail: a
loop `x_u = π(x_u)` with `π` fixed-point-free is never satisfied.

*Integrality.* If `U` has integer weights, multiply every weight of `O_c U` by
`N = vol · k · den(c)`. The original weights become `N w_e`, and the overlay
weights become `den(c) c deg(u) deg(v)`, both integers. Values and λ_2 are
invariant under uniform scaling. When `c` and `k` are constants, all
multiplicities are polynomial in the size of `U`, and the overlay adds
`k n(n−1)/2` distinct constraints. So `O_c` is a polynomial-time map on
constraint multisets.

## (3) The overlay: spectral gap

Put `p_u = deg(u)/vol` and `p_max = max_u p_u`. In `O_c U`, the new weight
between `u != v` is `β_uv`, so

```text
deg'(u) = deg(u) + c deg(u)(vol − deg(u))/vol = deg(u)(1 + c(1 − p_u)),
Q_'(f) = Q_A(f) + Q_B(f),   Q_B(f) = (c/(2 vol)) sum_(u,v) deg(u)deg(v)(f_u − f_v)^2
       = c ( ||f||_D^2 − vol μ^2 ),   μ = sum_u deg(u) f_u / vol.
```

Take `f != 0` with `sum_u deg'(u) f_u = 0`. That constraint reads
`(1+c) vol μ = c sum_u deg(u) p_u f_u`. By Cauchy--Schwarz,
`|sum_u deg(u) p_u f_u| <= (sum_u deg(u) p_u^2)^(1/2) ||f||_D`, and
`sum_u deg(u) p_u^2 <= p_max^2 vol`. So

```text
vol μ^2 = c^2 (sum deg p f)^2 / ((1+c)^2 vol) <= (c p_max/(1+c))^2 ||f||_D^2.
```

Also `deg' <= (1+c) deg`, so `||f||_(D')^2 <= (1+c) ||f||_D^2`. Since
`Q_A >= 0`, (0) gives

```text
λ_2(O_c U) >= c (1 − (c p_max/(1+c))^2) / (1+c).
```

* *General.* `p_max <= 1` gives `c((1+c)^2 − c^2)/(1+c)^3 = c(1+2c)/(1+c)^3`.
* *Loop-free.* `deg(u) = sum_(v != u) A_uv <= sum_(v != u) deg(v)`, so
  `p_max <= 1/2`. Then `1 − (c/(2(1+c)))^2 >= 3/4`, giving `3c/(4(1+c))`.
* *Regular, degree `d`.* `p_u = 1/n`, so `deg' = d(1 + c(1 − 1/n))` is constant
  and the overlay is regular (each new weight is `cd/(nk)`). The constraint
  `sum deg' f = 0` forces `μ = 0`, so `Q_B(f) = c ||f||_D^2`. With
  `||f||_(D')^2 <= (1+c)||f||_D^2` this gives `λ_2 >= c/(1+c)`.

## (4) Padding

For `m >= 1`, `U ⊗ m` has alphabet `Γ × Z_m` and constraints
`(x_v, b_v) = (π_e(x_u), b_u)`, with the same weights and the same graph. A
labeling `(x, b)` satisfies a constraint only if `x` does, so
`val(x, b) <= val(x)`. Constant `b` gives equality. So `opt(U ⊗ m) = opt(U)`,
the constraint graph and λ_2 are unchanged, loop-freeness and regularity are
unchanged, and the alphabet size is `km`. When `Γ = F_2^l` and
`π_e(x) = T_e x + b_e` is affine, the padded alphabet is
`F_2^l × F_2^(l') = F_2^(l+l')` with `π_e ⊕ id`, still affine with invertible
linear part.

## (5) Proof of (K2)

Assume UGC as in the root claim: for `0 < eps' < 1/2` there is `K` such that
`Gap-UG[1−eps', eps']` on `K` letters is NP-hard; take `Γ = Z_K`.

Fix `0 < eps < 1/2` and a rational `c in [9 eps/20, eps/2]`. Apply UGC at
`eps' = eps/2` to get `K`. Then choose `m` with `Km >= 2/eps`. The map is
`U ↦ O_c(U ⊗ m)`, polynomial by (2).

* *Completeness.* `opt >= 1 − eps/2` gives
  `opt' >= (1 − eps/2)/(1 + eps/2) >= 1 − eps`, since
  `(1 − eps)(1 + eps/2) = 1 − eps/2 − eps^2/2`.
* *Soundness.* `opt <= eps/2` gives `opt' <= max(eps/2, 1/(Km)) <= eps/2`.
* *Gap.* `λ_2 >= c(1+2c)/(1+c)^3 = c g(2c)`, where
  `g(t) = (1+t)/(1+t/2)^3`. Since `(log g)'(t) = 1/(1+t) − 3/(2+t) < 0` for
  `t >= 0`, and `2c <= eps < 1/2`, we have `g(2c) >= g(1/2) = 1.5/1.25^3 = 0.768`.
  So `λ_2 >= 0.45 · 0.768 eps > eps/4`.

Every output then has `λ_2 >= eps/4`, and YES outputs have ratio
`λ_2/(1 − opt') >= (eps/4)/eps = 1/4`.

*Loop-free regular variant.* Assume UGC on loop-free regular instances. Padding
is not needed: `opt' <= opt <= eps/2` by (2), and (3) gives regular outputs with
`λ_2 >= c/(1+c) >= (9 eps/20)/(1 + 1/4) = 0.36 eps >= eps/3`.

## (6) Proof of (K3)

By `unique-games-hard-at-completeness-one-half`, for every `eps > 0` there is `l`
with `Gap-UG[F_2^l]((1−eps)/2, eps)` NP-hard. Its constraints are
`T x_i + T' x_j = b` with `T, T'` invertible, that is `x_j = T'^(−1)(T x_i + b)`,
which is affine with invertible linear part. Choose `l'` with `2^(l+l') >= 1/eps`,
and apply `O_1(U ⊗ 2^(l'))` over `Γ = F_2^(l+l')`.

The overlay constraints `x_v = x_u + a` have the same linear form with
`T = T' = I` in characteristic 2, and padding keeps the linear form by (4). So
the outputs are linear games over `F_2^(l+l')`. By (2) and (4):

* YES outputs: `opt' >= ((1−eps)/2)/2 = (1−eps)/4`;
* NO outputs: `opt' <= max(eps, 2^(−(l+l'))) = eps`;
* all outputs: by (3), `λ_2 >= 1·3/8 = 3/8`.

Loops in the source are allowed, since the general bound was used.

## (7) Proof of (K4)

Let `μ = vol(S)/vol in (0,1)` and `f = 1_S − μ`. Then
`sum_u deg(u) f_u = vol(S) − μ vol = 0`, and `f != 0`.

```text
Q_A(f) = w(E(S, V∖S)) = Φ(S) vol(S) = Φ(S) μ vol,
||f||_D^2 = vol(S)(1−μ)^2 + (vol − vol(S)) μ^2 = vol μ(1−μ).
```

By (0), `λ_2 <= Φ(S)/(1−μ) <= η/(1−μ)`. On a `d`-regular graph the root SSEH
claim's `Φ(S) = |E(S, V∖S)|/(d|S|)` is this `Φ(S)`, and `μ(S)` is the volume
fraction. So a YES instance of `Gap-Small-Set-Expansion(η, δ)`, which has some
`S` with `μ(S) = δ` and `Φ(S) <= η`, has `λ_2 <= η/(1−δ)`.

## Replay

`experiments/ugc-calibration-2026-09-17/check_shift_overlay.py` checks (2) and
(3) in exact rational arithmetic (the λ_2 floors in floating point, tolerance
`1e-9`) on 720 random cases: `n in {3,4,5}`, `k in {2,3}`, regular, looped and
loop-free games, `c in {1/20, 1/4, 1, 3}`. It also confirms that looped games
below `1/k` occur, so the `max` in the soundness bound is needed. Output:
`cases=720 fails=0 looped games with val < 1/k: 20`, `ALL PASS`. The replay is a
check, not part of the proof.
