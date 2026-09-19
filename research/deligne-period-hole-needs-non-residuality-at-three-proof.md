---
rg: 2
id: deligne-period-hole-needs-non-residuality-at-three-proof
kind: route
title: Tensor a separating tower of exact metaplectic models with Dadarlat's winding model and check every recorded one-third invariant
target: deligne-period-hole-needs-non-residuality-at-three
requires: [metaplectic-half-class-has-an-exact-finite-model, dadarlat-linear-groups-have-nonzero-h2-windings, sp4-quasirep-windings-budget-and-saturation, deligne-sep7-norm-parameter-closed-subgroup, deligne-triple-cover-fd-central-invisibility, deligne-maslov-tensor-functors-are-asymptotically-regular]
---

Notation as in the target. `E_infinity = Gamma x_b Z` has product `(g,j)(h,l) = (gh, j + l + b(g,h))` and
central generator `zeta = (e,1)`. Its quotient `E_2 = E_infinity/<zeta^2>` has image `z` of `zeta`, with `z^2 = 1`.
Hats are the lifts `g^ = (g,0)`. `tr` is the normalized trace. `[A,B] = A B A* B*`, and for a unital map `pi`,
`W_r(pi) = prod_i [pi(a_i), pi(b_i)]`. When `||W_r(pi) - 1|| < 2`, `kappa_r(pi) = (1/2 pi i) Tr log W_r(pi)`, which
is an integer because `det W_r(pi) = 1`.

**Step 1: a separating tower of exact half-models.** By `metaplectic-half-class-has-an-exact-finite-model`, `E_2`
is residually finite and some finite quotient detects `z`. `E_2` is countable, so there are finite-index normal
subgroups `K_1 > K_2 > ...` with `z not in K_1` and `intersection K_n = 1`. Put `F_n = E_2/K_n`. Let `lambda_n` be
its left regular representation on `l^2(F_n)`, and `p_n = (1 - lambda_n(z))/2`, a central projection of trace
`1/2`. Set

```text
W_n(g) = lambda_n(g^) p_n    on    V_n = p_n l^2(F_n),     dim V_n = |F_n|/2.
```

Since `g^ h^ = z^(b(g,h)) (gh)^` and `lambda_n(z) = -1` on `V_n`, we get `W_n(g) W_n(h) = (-1)^(b(g,h)) W_n(gh)`
exactly. So `W_n` is an exact projective representation of class `1/2`, and `W_n(e) = I`.

**Step 2: its traces are central-regular.** For `x in F_n`, `tr(lambda_n(x) p_n) = 2 tr(lambda_n(x)(1 - lambda_n(z))/2)`,
normalized on `V_n`. This equals `delta_(x,e) - delta_(x,z)`. Let `g in Gamma` with `g != +-I`. Then `g^` is
neither `e` nor `z`, and neither is its image in `F_n` once `n` is large, since the tower separates the points
`g^`, `g^ z^(-1)` of `E_2` from `e`. So `tr W_n(g) = 0` for large `n`. The same holds at `g = -I`, whose lift is
not in `{e, z}` either. Hence every tracial limit of `W` vanishes off `g = I`: it is the average of the two
central-regular traces of the half-fibre. Also `dim V_n -> infinity`, since `|F_n| -> infinity`.

**Step 3: Dadarlat's winding model and the product.** By Step 0 of `sp4-quasirep-windings-budget-and-saturation-proof`
there is a relator `r = prod_(i<=g) [a_i, b_i]`, trivial in `Gamma`, with `prod [a_i^, b_i^] = zeta^k` and
`k != 0`. Its class `x = [r] in H_2(Gamma; Z)` pairs to `k` with the Maslov class, so it is non-torsion.
`dadarlat-linear-groups-have-nonzero-h2-windings` quotes Dadarlat's Theorem 3.2 and its sentence on linear groups.
Applied to `x`, they give unital `D_n : Gamma -> U(k_n)` with `||D_n(st) - D_n(s)D_n(t)|| -> 0`, and
`wn det((1-t) + t W_r(D_n)) != 0` for large `n`.

The quantity `W_r(D_n)` tends to `1`. Once `||W_r(D_n) - 1|| < 1`, the winding of `t -> det((1-t) + t X)` equals
`(1/2 pi i) Tr log X`: each eigenvalue `mu` of `X` contributes the principal argument of `mu`, along the segment
from `1` to `mu`. So `kappa_r(D_n) != 0` for large `n`. Put

```text
M_n = W_n (x) D_n : Gamma -> U(dim V_n * k_n).
```

Then `M_n(g)M_n(h) - e(b(g,h)/2) M_n(gh) = (-1)^(b(g,h)) W_n(gh) (x) (D_n(g)D_n(h) - D_n(gh))`, so `M` is a
`1/2`-model.

- (I1): `M^(x 2)` has multiplier `1`.
- (I2): `tr M_n(g) = tr W_n(g) tr D_n(g) -> 0` for `g != e`, by Step 2 and `|tr D_n| <= 1`. The tensor-functor
  consequences follow verbatim, by the proof of items 2--4 of `deligne-maslov-tensor-functors-are-asymptotically-regular`,
  which uses only this trace property.
- (I3): the dimension of `M_n` tends to infinity.
- (X): holds, via `W_1`.

**Step 4: winding after exact untwisting (I5).** Commutators and products are multiplicative for tensor products,
so `W_r(A (x) B) = W_r(A) (x) W_r(B)`. The map `conj(W_n) (x) W_n` has multiplier `(-1)^b (-1)^b = 1`, so it is an
honest representation. Its relator value is therefore its value at `prod[a_i, b_i] = 1`, namely `I`. Hence

```text
W_r(conj(W_n) (x) M_n) = I_(m_n) (x) W_r(D_n),      m_n = (dim V_n)^2,
kappa_r(conj(W_n) (x) M_n) = m_n kappa_r(D_n) != 0.
```

**Step 5: `M` is far from every exact half-representation (I4).** Let `rho` be an exact projective representation
of class `1/2` on the space of `M_n`, and let `delta = max_(y in {a_i, b_i}) ||M_n(y) - rho(y)||`. Suppose
`4 g delta + ||W_r(D_n) - 1|| < 2`. For each letter `y`, put `A_t(y) = M_n(y) exp(t L_y)` for `t in [0,1]`, where
`L_y` is the principal logarithm of `M_n(y)* rho(y)`. Since `|e^(i t s) - 1| <= |e^(i s) - 1|` for `|s| <= pi` and
`t in [0,1]`, we have `||A_t(y) - M_n(y)|| <= delta`. Hence:

- `W_r(conj(W_n) (x) A_t)` is a product of commutators, so its determinant is `1`;
- it depends continuously on `t`;
- it lies within `4 g delta` of `W_r(conj(W_n) (x) M_n) = I (x) W_r(D_n)`, so within distance `< 2` of `1`.

Therefore `kappa_r` is defined along the path. It is continuous and integer valued, hence constant. At `t = 1` the
map is `conj(W_n) (x) rho`, which has multiplier `1`. It is an honest representation, so its relator value is `I`
and its winding is `0`. At `t = 0` the winding is `m_n kappa_r(D_n) != 0`, by Step 4, a contradiction. Since
`W_r(D_n) -> 1`, this gives `delta >= (2 - o(1))/(4g) = 1/(2g) - o(1)`, uniformly in `rho`. In particular `M` is
not asymptotically close to any sequence of exact half-representations, nor to any `E (x) V` with `E` exact and
`V` honest. It is exactly of the form `E (x) V` with `E` exact and `V` an untwisted asymptotic homomorphism.

**Step 6: the one-third side.** Let `U` be any `1/3`-model.
- (I1): `U^(x 3)` has multiplier `e(b) = 1`.
- (I2): this is `deligne-maslov-tensor-functors-are-asymptotically-regular`.
- (X) fails: an exact finite-dimensional projective representation of class `-1/3 = 2/3` would be a
  finite-dimensional representation of `E_3` with `z` acting by a primitive cube root of unity. This contradicts
  `deligne-triple-cover-fd-central-invisibility`.
- (I3): suppose `d_n = d` along a subsequence. `Gamma` is countable and `U(d)` is compact, so a diagonal
  subsequence converges at every `g`, and the limit is an exact projective representation of class `1/3`. This
  contradicts the failure of (X), after conjugating.
- (I4): holds vacuously, since there are no exact representations of class `1/3`.
- (I5): has no content at `1/3`, for the same reason.

So (I1)--(I4) hold for every `1/3`-model, and (X) is the one listed property on which the two parameters differ.

**Step 7: calibration.** Let `A` be a residual-blind argument in the sense of the target: from a `1/l`-model with
(I1)--(I5), using `l` only through (I1) and only facts about `Gamma` valid at `l = 2` and `l = 3`, it concludes
`P_op = R/Z`. By Steps 3--5, `M` is such a model at `l = 2`, and it exists unconditionally. So `A` proves
`P_op = R/Z`. By `deligne-sep7-norm-parameter-closed-subgroup`, this gives `1/3 in P_op`, i.e. a `1/3`-model exists,
i.e. `E_3` is MF. That is the negation of `deligne-triple-cover-exact-mf-radical`, whose reformulation is
`1/3 not in P_op`. It also excludes the branch `P_op = R/Z` that `sp4-quasirep-windings-are-sublinear` must rule
out, so it refutes that node too. So on every flagship route through the period hole, a proof of the hole is not
residual-blind: some step must use the failure of (X) at `3`, which is Deligne's three-adic input. QED.

**Scope, stated honestly.** "Residual-blind" is a syntactic class. The theorem does not show that the period hole
is false or unprovable. It shows that every proof needs an ingredient distinguishing `M` from a `1/3`-model, and
the only listed such ingredient is (X). Nothing here decides whether `P_op` is finite.
