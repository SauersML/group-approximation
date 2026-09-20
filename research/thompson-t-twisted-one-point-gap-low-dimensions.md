---
rg: 2
id: thompson-t-twisted-one-point-gap-low-dimensions
kind: claim
title: "The twisted one-point gap of Thompson's T: exact pairs with U^4 = -1 and V^3 = 1 have T-defect at least 2 sin(pi/24) in dimensions 1 and 2, attained only by characters; every fixed dimension has a positive gap; and 2.A_6 = SL(2,9) satisfies the pentagon and r_2 exactly with the twist, so r_1 alone carries the twisted gap"
distinct_from:
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the untwisted gap delta_n over nontrivial exact pairs A^4 = B^3 = 1, with delta_1 = 2 sin(pi/12); this is the twisted gap mu_n over exact pairs U^4 = -1, V^3 = 1, where every pair is nontrivial, mu_1 = 2 sin(pi/24), and dimension 2 does not improve on dimension 1.
  thompson-t-pentagon-winding-rigidity: that is a winding statement about (BA)^5 on untwisted near-relator pairs; this is a norm gap on twisted exact pairs and uses no winding number.
  thompson-t-pentagon-winding-sandwich: that computes the Euler pairing e((ba)^5) = 3, e(a^4) = e(b^3) = 1 and uses it for the sandwich; this uses the same numbers only to turn an exact twisted pair into a representation of T-bar with z -> -1.
  thompson-t-has-full-mf-radical: that is the target, equivalent to inf_n mu_n > 0; this proves mu_n > 0 for each n, computes mu_1 and mu_2 exactly, and does not decide the infimum.
  lifted-thompson-t-is-not-mf: that is the open statement that every corona representation of T-bar kills z; this is the finite-dimensional, fixed-dimension shadow of its one-point form, plus a relator-drop computation.
artifacts:
  - experiments/thompson-t-twisted-one-point-2026-09-17/census.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/control.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/dim2_certificate.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_dim2_certificate.json
  - experiments/thompson-t-twisted-one-point-2026-09-17/sl2_twisted.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_sl2_twisted.json
  - experiments/thompson-t-twisted-one-point-2026-09-17/sl2_9_irreps.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_sl2_9_irreps.json
  - experiments/thompson-t-twisted-one-point-2026-09-17/sl2_9_generation.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_sl2_9_generation.json
  - experiments/thompson-t-twisted-one-point-2026-09-17/calib.py
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_calib.txt
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_census_012.txt
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_census_01.txt
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_census_02.txt
  - experiments/thompson-t-twisted-one-point-2026-09-17/out_census_012_n3_r24.txt
---

**ESTABLISHED (written proof below; part (B) is computer-assisted by a grid-plus-Lipschitz certificate;
part (D) is an exact finite-group computation evaluated in floating point to 1e-14). Unreviewed. Not
Lean-verified.** The census in "What is not established" is numerical and proves only upper bounds.

## Setting

Use the Lochak--Schneps words of `thompson-t-lochak-schneps-presentation`, with `a, b` the generators of
orders 4 and 3:

```text
X = b a b,   J = a^2,   W = a^2 b^2 a^2,   r_1 = [X, J X J^-1],   r_2 = [X, W X W^-1],   r_P = (b a)^5.
```

For unitaries, `||[x, y] - 1|| = ||x y - y x||`, so the commutator convention does not matter.

A *twisted exact pair* is `(U, V)` in `U(n)^2` with `U^4 = -1` and `V^3 = 1` exactly. Its *twisted defect* is

```text
M(U, V) = max( ||(V U)^5 - 1||, ||r_1(U, V) - 1||, ||r_2(U, V) - 1|| ),     mu_n = min over U(n) of M.
```

The minimum exists because the set of twisted exact pairs in `U(n)` is compact and `M` is continuous.
For `S` a subset of `{P, 1, 2}`, `M_S` and `mu_n^S` use only the words in `S`.

**Why `mu_n` is the right quantity.** The w19 node `thompson-t-pentagon-winding-rigidity-equals-full-radical`
(on main, not in this worktree; item 5) shows that `T` is MF iff some sequence of unitary pairs has
`U^4 -> -1`, `V^3 -> 1`, `(VU)^5 -> 1` and `r_i -> 1` in norm. Spectral rounding of `U` to the odd 8th roots
and of `V` to the cube roots moves each by at most a constant times its defect. So

```text
T is MF   <=>   inf_n mu_n = 0,     and     T is not MF   <=>   inf_n mu_n > 0.
```

This node studies `mu_n` at fixed `n`.

**Reading convention.** Transposition reverses words and preserves norms:
`w(U, V)^T = w^rev(U^T, V^T)`, and `U^T, V^T` are again a twisted exact pair. So the set of values of `M`,
and hence `mu_n`, is the same under both reading conventions. Matrices below use the matrix-product
convention: `ba -> V U` and `X -> V U V`.

## Statement

**(A) Dimension 1.** `mu_1 = 2 sin(pi/24) = 0.2610523844...`. Exactly two characters attain it:
`(u, v) = (e^{i pi/4}, omega^2)` and `(u, v) = (e^{-i pi/4}, omega)`, where `omega = e^{2 pi i/3}`.

**(B) Dimension 2 (computer-assisted).** `mu_2 = mu_1`. Every minimiser in `U(2)` is unitarily
equivalent to a direct sum of two characters, each of them one of the two optimal characters of (A).
Every pair that is not such a direct sum has `M > mu_1`. Every irreducible pair outside the single
delicate family below has `M >= 0.4698`. Irreducible pairs in the delicate family approach `mu_1` only
near the reducible optimal point. So dimension 2 gives no improvement over dimension 1.

**(C) Every fixed dimension.** `mu_n > 0` for every `n >= 1`.

**(D) Relator drop: `r_1` carries the gap.** `SL(2,9) = 2.A_6` contains pairs `(a, b)` with all of these:
- `a^4 = -I`, `b^3 = I`, `(ba)^5 = I` and `r_2(a, b) = I`;
- `r_1(a, b) != I`.

In each faithful irreducible representation of `SL(2,9)` (degrees 4, 4, 8, 8, 10, 10), such a pair gives a
twisted exact pair with the following defects:
- `(VU)^5 = 1` and `r_2 = 1` exactly;
- `||r_1 - 1|| = sqrt 2`.

Hence `mu_4^{P,2} = 0`. The same holds in degrees 8 and 10.

No pair in `SL(2,q)` with `a^4 = -I`, `b^3 = I`, `(ba)^5 = I` has `r_1 = I`, for
`q` in `{9, 25, 7, 11, 13, 17, 19, 23, 29, 31}`. As (C) requires, no such pair has both `r_1 = r_2 = I`.

Together with the exact pentagon-only solution in `SU(2)` (the `Delta(4,3,5)` lift, `mu_2^{P} = 0`), this
gives the following hierarchy:

```text
mu_2^{P} = 0,   mu_4^{P,2} = 0,   mu_n^{P,1,2} = mu_n > 0 for every n,   mu_1 = mu_2 = 2 sin(pi/24).
```

## Proof

**(A).** In dimension 1, `r_1` and `r_2` are commutators of scalars, so they equal 1. Only the pentagon
counts. Write `u = e^{2 pi i (2k+1)/8}` and `v = e^{2 pi i j/3}`. Then `(vu)^5 = e^{2 pi i N/24}` with
`N = 5 (3(2k+1) + 8j)`.

`N` is odd, so `N` is not `0 mod 24`, and `|(vu)^5 - 1| >= |e^{2 pi i/24} - 1| = 2 sin(pi/24)`. Equality
holds iff `N = +-1 mod 24`. Since `5 * 5 = 25 = 1 mod 24`, this means `3(2k+1) + 8j = +-5 mod 24`.

Checking the twelve pairs `(k, j)`:
- `k = 0`: the values are `3, 11, 19`, so `j = 2` works (19 = -5).
- `k = 1`: the values are `9, 17, 1`; none works.
- `k = 2`: the values are `15, 23, 7`; none works.
- `k = 3`: the values are `21, 5, 13`, so `j = 1` works.

So the minimisers are `(e^{i pi/4}, omega^2)` and `(e^{7 i pi/4}, omega) = (e^{-i pi/4}, omega)`.

**(B), reduction to one parameter.** Let `(U, V)` be a twisted exact pair in `U(2)`.

*Case 1: `U` or `V` is scalar.* Then `U` and `V` commute and diagonalise together. The pair is a
direct sum of two characters, and `M` is the larger of the two character defects. So `M >= mu_1`, with
equality iff both characters are optimal characters of (A).

*Case 2: neither is scalar.* Conjugate so that `U = diag(u1, u2)` with `u1 != u2`, both odd 8th roots.
Then `V = Y diag(v1, v2) Y*` with `v1 != v2` cube roots. The line `Y e_1` is a point of `CP^1`.

Conjugating by the diagonal torus, which fixes `U`, rotates this sphere about the axis through
`e_1, e_2`. So `Y` may be taken to be `R(theta)`, the real rotation by `theta/2`, with `theta` in `[0, pi]`.
The phases of the columns of `Y` do not change `V`.

This gives 6 unordered `{u1, u2}` times 6 ordered `(v1, v2)`, that is 36 one-parameter families
`f(theta) = M(U, V(theta))`.

**(B), Lipschitz bound.** `dV/dtheta = (1/2)[K, V]` with `K = R'(0)` and `||K|| = 1`, so
`||dV/dtheta|| <= 1`. The word `(VU)^5` has 5 letters `V`. `X` has 2 letters `V`, `J X J^-1` has 2, and
`W X W^-1` has 6.

The map `(x, y) -> x y - y x` has derivative bounded by `2(||x'|| + ||y'||)`. So:
- the pentagon defect is 5-Lipschitz;
- the `r_1` defect is 8-Lipschitz;
- the `r_2` defect is 16-Lipschitz;
- `f` is 16-Lipschitz.

On a grid of step `h`, `f >= min_grid f - 8h`.

**(B), the generic families.** `dim2_certificate.py` evaluates `f` on the grid `h = pi/20000` for the
34 families other than the delicate one and its mirror, described below. It certifies
`f >= 0.46984 > mu_1` on each of them (`out_dim2_certificate.json`). The smallest family minimum is
`0.47110`, at `U = diag(e^{i pi/4}, e^{5 i pi/4})`, which is not in the delicate family.

**(B), the delicate family.** Take `U = diag(e^{i pi/4}, e^{-i pi/4})` and `(v1, v2) = (omega^2, omega)`.
This is the only family with an endpoint that is a direct sum of two optimal characters, at
`theta = 0`. Its mirror `(v1, v2) = (omega, omega^2)` is the same family: conjugating by
`diag(1, -1)`, which commutes with `U`, sends `theta` to `pi - theta` (checked to `3.5e-16`).

Here `det U = det V = 1`, so `VU` lies in `SU(2)`. Its eigenvalues are `e^{+-i phi}` with
`2 cos phi = tr(VU)`. Since `(R D R^T)_{11} = (v1+v2)/2 + (v1-v2)/2 cos theta`, one gets

```text
tr(V U) = (u1+u2)(v1+v2)/2 + (u1-u2)(v1-v2)/2 cos theta = -sqrt2/2 + (sqrt6/2) cos theta.
```

The script checks this to `4e-16`. So `phi` increases strictly from `5 pi/12` at `theta = 0` to
`11 pi/12` at `theta = pi`.

The matrix `(VU)^5 - 1` is normal with eigenvalues `e^{+-5 i phi} - 1`, so the pentagon defect is
`2|sin(5 phi/2)|`. For `5 phi` in `[25 pi/12, 55 pi/12]`, the equation `2|sin(5 phi/2)| = mu_1` means
`5 phi = +-pi/12 mod 2 pi`. That gives `5 phi` in `{25 pi/12, 47 pi/12, 49 pi/12}`, and the pentagon defect is
`< mu_1` exactly when `5 phi` lies in `(47 pi/12, 49 pi/12)`.

So, on the delicate family:
- outside the closed window `theta` in `[2.33467, 2.48519]`, `f >= mu_1`, with equality only at `theta = 0`;
- on the window plus a collar of 0.01, the grid gives `max(||r_1 - 1||, ||r_2 - 1||) >= 1.7441 > mu_1`.

Hence `f > mu_1` for `theta > 0`, and `f(0) = mu_1`.

*The pentagon-only solution, `mu_2^{P} = 0`.* By continuity and monotonicity, `phi = 4 pi/5` at exactly one
`theta_*` in the window. Here `phi = 4 pi/5` lies in `[5 pi/12, 11 pi/12]`. At `theta_*`, `(VU)^5` is
diagonalisable with both eigenvalues `e^{+-4 pi i} = 1`, so `(VU)^5 = 1` exactly. This is the `SU(2)`
lift of `Delta(4,3,5)`. `control.py` plants it, and there the `r_1` defect is `1.2555` and the `r_2` defect
is `1.8973`.

The certificate uses floating-point evaluation, not interval arithmetic. Its margins are `0.2088` and
`1.483` above `mu_1`, against rounding errors of order `1e-15`.

**(B), conclusion.** Cases 1 and 2 give `mu_2 = mu_1`. Equality holds only for a direct sum of optimal
characters: in Case 1 directly, and in Case 2 only at `theta = 0` of the delicate family, which is again
such a direct sum. An irreducible pair lies in Case 2 with `theta` in `(0, pi)`, and there `f >= 0.4698` on
the generic families. On the delicate and mirror families, off the window `f` is at least the pentagon defect,
which is `>= mu_1`; on the window `f >= 1.744`.

The bound `M >= 0.4698` for *every* irreducible pair holds only on the generic families. On the delicate
family, near `theta = 0`, `f` tends to `mu_1`. So the correct statement is this: every irreducible pair has
`M > mu_1`, and the infimum of `M` over irreducible pairs is `mu_1`, approached only near the reducible
optimal point.

**(C).** The set of twisted exact pairs in `U(n)` is compact and `M` is continuous, so it suffices to show
that `M` never vanishes. Suppose `M(U, V) = 0`. Transposing if needed (see "Reading convention"), the
five words are then trivial in the convention of `thompson-t-pentagon-winding-sandwich-proof`, (3).

*Step 1: a presentation of T-bar.* That node fixes lifts `a-bar(x) = x + 1/4` and `b-bar` with
`b-bar(0) = 1/2` in `T-bar`, the group of lifts to `R` of elements of `T`. It computes, in exact
arithmetic, the translation numbers
- `e(a^4) = 1` and `e(b^3) = 1`;
- `e(r_1) = e(r_2) = 0`;
- `e((ba)^5) = 3`.

So `a-bar^4 = z`, `b-bar^3 = z`, `(b-bar a-bar)^5 = z^3` and `r_i(a-bar, b-bar) = 1`, where `z` is translation
by 1. Let

```text
G-hat = < a, b, z | z central, a^4 = z, b^3 = z, (ba)^5 = z^3, r_1 = r_2 = 1 >.
```

- **Surjective.** The map `G-hat -> T-bar` given by `a -> a-bar`, `b -> b-bar`, `z -> z` is onto,
  because `T-bar` is generated by lifts of the generators of `T` together with the central `Z`.
- **Injective.** `G-hat / <z>` is the Lochak--Schneps presentation of `T`
  (`thompson-t-lochak-schneps-presentation`). So the composite `G-hat -> T-bar -> T` has kernel `<z>`,
  and the kernel of `G-hat -> T-bar` lies in `<z>`. But `z^k` maps to translation by `k`, so that kernel
  is trivial.

Hence `G-hat = T-bar`.

*Step 2: the representation.* Put `rho(a) = U`, `rho(b) = -V` and `rho(z) = -1`. The relations hold:
- `U^4 = -1`;
- `(-V)^3 = -1`;
- `(-V U)^5 = -(VU)^5 = -1 = (-1)^3`;
- `r_1` and `r_2` are unchanged by `V -> -V`, because `X = b a b`, `J = a^2` and `W = a^2 b^2 a^2` each
  contain an even number of letters `b`.

So `rho: T-bar -> U(n)` is a homomorphism with `rho(z) = -1`.

*Step 3: it is trivial.* `rho(T-bar)` is a finitely generated linear group, so it is residually finite
(`finitely-generated-linear-groups-are-residually-finite`, Malcev). It is a quotient of `T-bar`, which
has no proper finite-index subgroup (`lifted-thompson-t-perfect-centre-cubically-elliptic`). So it has
none either, as in (L0) of `lifted-thompson-t-escapes-haagerup-permanence-closure-proof`. A residually
finite group with no proper finite-index subgroup is trivial, so `rho = 1`. This contradicts
`rho(z) = -1`.

Hence `M > 0` on the compact set, and `mu_n > 0`.

*A consequence for finite groups.* Take a pair in `SL(2,q)` with `a^4 = -I`, `b^3 = I` and `(ba)^5 = I`.
A faithful irreducible representation sends `-I` to `-1`, so it turns the pair into a twisted exact
pair. By (C), `r_1` and `r_2` cannot both equal `I`. The same holds in any finite group, for any
irreducible representation in which `a^4` acts by `-1`. (D) confirms this independently.

**(D).** `sl2_twisted.py` enumerates `SL(2,q)` in exact finite-field arithmetic, with `F_9 = F_3[t]/(t^2 - 2)`
and `F_25 = F_5[t]/(t^2 - 2)`. For one `a` in each conjugacy class with `a^4 = -I`, and every `b` of
order 3 with `(ba)^5 = I`, it classifies `r_1(a, b)` and `r_2(a, b)` as `I`, `-I` or other
(`out_sl2_twisted.json`).

| q | pairs | outcome |
|---|---|---|
| 9 | 32 | 16 with `r_2 = I`, `r_1` other; 16 with both other |
| 25 | 48 | all other/other |
| 31 | 128 | all other/other |
| 7, 17, 23 | 0 | no element of order 5 exists, since `5` does not divide `|SL(2,q)|` |
| 11, 13, 19, 29 | 0 | no `a` with `a^4 = -I` exists |

`sl2_9_irreps.py` splits the regular representation of `SL(2,9)` (order 720). It restricts to the
`-I -> -1` part and takes eigenspaces of a random Hermitian element of the commutant, obtained by
averaging over left translations. This yields the six faithful irreducible representations, of degrees
4, 4, 8, 8, 10, 10.

For each of them, and all 32 pairs, it evaluates `U`, `V` and the defects (`out_sl2_9_irreps.json`).
The exactness errors `||U^4 + 1||`, `||V^3 - 1||` and `||(VU)^5 - 1||` are at most `1.8e-14`.

| degree | pairs with `r_2 = I` | the other 16 pairs |
|---|---|---|
| 4 | `r_1 = sqrt 2 = 1.414214`, `r_2 = 0` | `r_1 = r_2 = 1.618034` |
| 8, 10 | `r_1 = sqrt 2`, `r_2 = 0` | `r_1 = r_2 = 2` |

In degree 4:
- `U` has spectrum `{e^{+-i pi/4}, e^{+-3 i pi/4}}`, each with multiplicity 1.
- `V` has spectrum `{1, 1, omega, omega^2}` in one representation and `{omega, omega, omega^2, omega^2}`
  in the other.

This gives `mu_4^{P,2} = mu_8^{P,2} = mu_10^{P,2} = 0`.

**Group-level form of (D).** Let `G-hat_{P,2}` be `G-hat` with the relator `r_1` deleted. The map
`a -> a`, `b -> -b` (with `a, b` the `SL(2,9)` pair above) and `z -> -I` is a homomorphism
`G-hat_{P,2} -> SL(2,9)`:
- `a^4 = -I`;
- `(-b)^3 = -I`;
- `(-ba)^5 = -I = (-I)^3`;
- `r_2` holds, because it has an even number of `b`s.

It is onto, because every one of the 32 pairs generates `SL(2,9)`: `|<a, b>| = 720`
(`sl2_9_generation.py`, `out_sl2_9_generation.json`). Hence `<a, -b> = <a, b>`.
So `z` has order 2 in a finite quotient of `G-hat_{P,2}`, while `G-hat = T-bar` has no nontrivial finite
quotient at all. **Deleting `r_1` from the lifted presentation creates a finite quotient that is
faithful on `<z>/<z^2>`.** No such quotient onto `SL(2,q)`, `q <= 31`, exists with `r_2` deleted. The listed `q` are
enumerated. The other `q` are trivial:
- `q = 3, 5`: there is no element of order 8;
- `q = 27`: `5` does not divide `|SL(2,27)| = 19656`;
- even `q`: `-I = I`.

## Relation to the main-branch relator-drop computation

The w19 node `thompson-t-pentagon-winding-rigidity-equals-full-radical` (on main, not in this worktree)
records, untwisted, that `Delta(4,3,5)/<<r_2>>` maps onto `A_6`. It notes there that finite witnesses
"carry only torsion `H_2`" and change no status.

(D) is the *twisted* lift of that witness, and it lands exactly on the one-point form of that node's
item 5, `lambda_0 = -1`. So `-1` lies in the twisted spectrum of `{a^4, b^3, r_P, r_2}`, attained
exactly in `U(4)`. It is excluded from the twisted spectrum of `{a^4, b^3, r_P, r_1, r_2}` in each fixed
dimension, by (C).

The torsion of the witness does not matter here, because the one-point form asks about `lambda = -1`,
which is itself torsion. Its `A_5` witness for `Delta/<<r_1>>` has `J -> 1`. It has no twisted lift at all,
because `2.A_5 = SL(2,5)` has no element with `a^4 = -I` (no elements of order 8).

## What is not established

**The infimum.** Nothing here bounds `inf_n mu_n` from below. The flagship `thompson-t-has-full-mf-radical`
is equivalent to `inf_n mu_n > 0`. (C) is the fixed-dimension shadow of that statement, and its constant is
not uniform: it comes from compactness.

**Conjecture (sharp twisted gap).** `mu_n = 2 sin(pi/24)` for every `n`. The minimisers would be direct
sums of the two optimal characters. This conjecture implies the flagship. It is supported only by the
census below, for `n <= 5`.

**Census (numerical; upper bounds only).** `census.py` minimises a Schatten-8 surrogate of `M` over
`V = Y D Y*`, with `U` diagonal of fixed eigen-type. It does this for every pair of eigen-types. Every
printed value is attained by an explicit feasible pair, so it is an upper bound for `mu_n`.

| run | n | restarts x iters | best `M` found | best non-character-type value |
|---|---|---|---|---|
| `out_census_012.txt` | 1..5 | 4 x 400 | `0.261052` for every n | `0.489892` (n=2, 3), `0.755243` (n=4), `0.490077` (n=5) |
| `out_census_012_n3_r24.txt` | 3 | 24 x 500 | `0.261052` | `0.489892` |

The minimum is always attained on eigen-types that contain a direct sum of optimal characters.
`out_census_01.txt` (pentagon and `r_1` only) and `out_census_02.txt` (pentagon and `r_2` only), at
4 restarts, also report `0.261052` for `n <= 4`.

**Calibration shows the low-restart census is under-sampled.** For `n = 4` in mode `P,2`, the exact
`2.A_6` solution of (D) has `M_{P,2} = 0`. The 4-restart census *missed* it and reported `0.261052`.
`calib.py`, with 48 restarts x 600 iterations on the correct eigen-type, finds it:
`9.4e-05` for V-type `(0,0,1,2)` and `4.1e-05` for `(1,1,2,2)` (`out_calib.txt`).

The same under-sampling shows up at `n = 2`. The census reports `0.489892` as the best generic value,
but the certificate of (B) finds generic families with minimum `0.47110`.

So a census value of `mu_1` at `n >= 3` is weak evidence for the conjecture. The census is consistent
with (A) and (B), but it cannot rule out an isolated exact or near-exact solution in dimension
`3 <= n <= 5`.

## What this changes

- **A class-killing obstruction for the one-point target.** Call a proof of `-1 ∉ Lambda` (item 5 of the
  main-branch equivalence node, i.e. of the flagship) *`r_1`-blind* if it uses only these hypotheses:
  - `U^4 = -1`, `V^3 = 1` (or approximately);
  - `(VU)^5 -> 1`;
  - `r_2 -> 1`.

  Every `r_1`-blind argument fails.
  - *Named invariant:* the twisted defect `M_{P,2}`.
  - *Death step:* (D). The faithful 4-dimensional representations of `2.A_6` give `M_{P,2} = 0` exactly,
    with the twist `z -> -1`.

  This kills, for example, any "rigidity of `Delta(4,3,5)` plus `r_2`" argument. It also kills any
  argument that applies a finite-group or residual-finiteness obstruction to
  `<a, b, z | z central, a^4 = z, b^3 = z, (ba)^5 = z^3, r_2>`, because that group has the finite quotient
  `SL(2,9)` with `z` of order 2. So the step of (C) that uses the absence of finite quotients cannot be
  run without `r_1`.

  Pentagon-only arguments were already dead: the `SU(2)` lift of `Delta(4,3,5)` has `mu_2^{P} = 0`. So
  **`r_1` is the load-bearing relator of the twisted gap**. This reverses the untwisted picture.
  - For the untwisted gap of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`, the main-branch node
    `thompson-t-defect-gap-central-square-locus` (not in this worktree) finds a 2-dimensional minimiser
    with `r_1` exact and gap `0.3491 < 2 sin(pi/12)`.
  - Here, dropping `r_1` is what kills the gap.

- **Twisted rigidity in low dimension.** Untwisted, dimension 2 lowers the gap below the character value.
  Twisted, it does not: `mu_2 = mu_1` exactly, and the minimisers are reducible. This gives an exact
  value of the one-point quantity beyond dimension 1. It makes the sharp conjecture `mu_n = 2 sin(pi/24)`
  a falsifiable decomposition of the flagship:
  - a certified computation of `mu_3`, or of `mu_4` restricted to the `2.A_6` eigen-types, can refute it;
  - proving it proves `T` not MF.

- **The fixed-dimension shadow is free.** (C) shows that `mu_n > 0` in each dimension follows from
  perfectness plus Malcev alone. So any non-uniform-in-`n` argument proves nothing beyond (C), and all
  content of the flagship is in the uniformity of the gap as `n -> infinity`.

- **Where to look for a counterexample.** A sequence with `mu_n -> 0` must satisfy `r_1` asymptotically.
  No `SL(2,q)`, `q <= 31`, supports an exact twisted `r_1`-solution even with `r_2` dropped. The next
  places to search are finite groups with elements of order 8 and 5 and a faithful central involution, and
  in each of them `{P, 1}` rather than `{P, 2}`: `2.A_7`, `2.S_6` variants, `SL(3,q)` central extensions,
  `Sp(4,q)`.
