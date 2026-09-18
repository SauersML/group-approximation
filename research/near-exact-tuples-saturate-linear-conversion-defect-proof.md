---
rg: 2
id: near-exact-tuples-saturate-linear-conversion-defect-proof
kind: route
title: A one-point phase twist of a permutation representation is a rank-k tuple whose u^L differs from every short word for u^L on exactly the L-point orbit segment
target: near-exact-tuples-saturate-linear-conversion-defect
requires: []
---

Notation as in the claim. `P = pi(u)`, `Q = pi(v)` with `v = e_13`, and `D = diag(lambda` at
`x_0`, `1` elsewhere`)`. All matrices below are monomial: permutation matrices times diagonal
unitaries. `|w|_u` is the number of letters `u^(+-1)` in a word `w`.

**Lemma A (telescoping).** Let `pi` be a representation of `Gamma` and `rho` a tuple with
`rank(rho(s) - pi(s)) <= r` for all `s` in a set `T` of generators, and `rho(s) = pi(s)` otherwise.
Then for every word `w`,
`rank(rho(w) - pi(w)) <= r |w|_T`, where `|w|_T` counts the letters from `T^(+-1)`.

*Proof.* Write `w = s_1 ... s_N` and telescope:
`rho(w) - pi(w) = sum_i rho(s_1...s_(i-1)) (rho(s_i) - pi(s_i)) pi(s_(i+1)...s_N)`. The terms with
`s_i` outside `T^(+-1)` vanish. For the others,
`rho(s)^(-1) - pi(s)^(-1) = rho(s)^(-1) (pi(s) - rho(s)) pi(s)^(-1)` also has rank `<= r`, and rank is
subadditive. QED.

If `w` is trivial in `Gamma` then `pi(w) = I`, which gives the noise floor
`rank(rho(w) - I) <= r |w|`.

**Part 1.** Take `T = {u}` and `r = 1`: `rho(u) - pi(u) = P(D - I)` has rank 1. For a relator `r`,
`pi(r) = I`, so Lemma A gives `rank(rho(r) - I) <= |r|_u`. Unitarity holds because `|lambda| = 1`.

**Part 2.** For a monomial matrix `M`, `rank(M - I)` is computed cycle by cycle. On a cycle of
length `l` whose phase product is `mu`, the block of `M - I` has rank `l` if `mu != 1` and `l - 1`
if `mu = 1`.

Compute `(PD)^L`. On `delta_x` it acts by `lambda^(c(x)) delta_(P^L x)`, where
`c(x) = #{0 <= i < L : P^i x = x_0}`. Since `(x_0)_2 = 1 != 0`, the point `x_0` lies on a `P`-cycle
of length exactly `p`. For `L <= p` we get `c(x) in {0, 1}`, and `c(x) = 1` exactly on the orbit
segment `S = {P^(-i) x_0 : 0 <= i < L}`, which has `L` distinct points. So

```text
rho(u)^L - pi(u)^L = P^L (D_L - I),   D_L = diag(lambda on S, 1 off S),
```

and its rank is `|S| = L`.

Now let `W = u^L` in `Gamma`. Then `pi(W) = P^L`, and by Lemma A
`rank(rho(W) - P^L) <= |W|_u`. So

```text
| rank(rho(u)^L - rho(W)) - L |  <=  |W|_u .
```

For `n >= 3` the word `W = [e_13^a, e_32^b]` equals `e_12^(ab)` in `SL_n(Z)` (Steinberg relation,
with `e_12` central in the Heisenberg group `<e_13, e_32>`). It has `|W|_u = 0`, so the conversion
defect is exactly `L`. For the LMR words, `|W_L|_u <= |W_L| = O(log^2 L)`.

**Part 3.** `P` and `Q` commute. Using `(PD)^L = P^L D_L`,

```text
[rho(u)^L, Q^L] = P^L D_L Q^L D_L^(-1) P^(-L) Q^(-L) = P^L D_L D'_L P^(-L),
```

with `D'_L = Q^L D_L^(-1) Q^(-L) = diag(lambda^(-1) on Q^L S, 1 elsewhere)`. So
`phi(L) = rank(D_L D'_L - I) = |S triangle Q^L S|`. Here `S = {x_0 - i e_1 : 0 <= i < L}`, and
`Q^L` adds `L (x)_3 e_1 = L e_1`, so `Q^L S = {x_0 + j e_1 : 1 <= j <= L}`. Modulo `p`, the offsets
`-(L-1), ..., 0` and `1, ..., L` are `2L` distinct residues when `2L <= p`. So the two sets are disjoint
and `phi(L) = 2L`. QED.

**Lemma B (distance from rectangle profile).** Let `b, c` be in `U(d)`, let `beta, gamma` be in
`U(m)`, and let `b', c'` commute on `C^d (+) C^m`. Put
`delta = max(rank(b' - b (+) beta), rank(c' - c (+) gamma))`. For every word `w` trivial in `Z^2`,
Lemma A (with `Gamma = Z^2`, `pi = (b', c')`) gives
`rank(w(b,c) - I) <= rank(w(b (+) beta, c (+) gamma) - I) <= delta |w|`. So `delta >= Lambda(b,c)`.
With the rectangle word `w = [x^s, y^t]` of length `2(s + t)` this gives the profile bound
`rank([b^s, c^t] - I) <= 2 delta (s + t)`. QED.

**The two known far families are quadratic.** The slit origami has
`rank([b^m, c^m] - I) = 2 m^2` for `1 <= m <= s = floor(L/2)`. The loop based at `(i,x,y)`
closes up to a sheet flip, and flips exactly when one of its two vertical legs (columns `x` and
`x + m`) crosses the slit row transition `0 -> 1` inside the slit columns `[0, s)` and the other does
not. That needs `y` in an `m`-element window of rows, and `x` in `[s - m, s)` or `[L - m, L)`. These
two column intervals are disjoint because `m <= s <= L - m`. So `2 * m * 2m = 4 m^2` squares move, in
sheet-swap 2-cycles, and the rank is `2 m^2`. This is the parity count of
`slit-origami-z2-pair-has-rank-distance-half-l-proof`, run at every scale `m`, and
`experiments/near-exact-noise-floor-2026-09-17/noise_floor.out` checks it for `L = 4, ..., 14`. The
dislocation dipole saturates the area law by its own computation. So both have
`Lambda >= phi(m)/(4m)` of order `m` up to the defect scale, and the linear law of
`sln-relators-force-linear-commutator-growth` excludes them as summands once `m > C_5 k / 2`.

**Verification.** `noise_floor.py` computes ranks exactly through the cycle and phase formula. It
treats `lambda` as generic by tracking integer exponents, and it cross-checks with numpy SVD for
`SL_3(Z/5)`. It covers `SL_3(Z/11)`, `SL_3(Z/13)` and `SL_4(Z/7)` with the full Steinberg
presentation (commutator relations plus the Weyl relator `(e_12 e_21^(-1) e_12)^4`). It checks:
- `pi` satisfies every relator;
- `rank(rho(r) - I) <= |r|_u` for every relator `r`;
- the conversion defect equals `L` for every factorization `ab = L`;
- `phi(L) = 2L` for `2L <= p`.

Output: `ALL OK`.
