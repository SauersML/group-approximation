# Corner rank data cannot contract the two-root deviation

Lane `w3-gate-bridge-a`. Target: `N_23 N_12 = 0` for characteristic-two rank models of
`EL_3(L_(F_2)(1,2))`, equivalently (corner locality, Corollary 2.4 of
`two-root-identity-nonsofic-mechanism-2026-09-12.md`) `rk(n_23(s_0) n_12(t_0)) = 0`.

The directive was to look for a rank identity pushing that product into a corner whose rank
**halves** under the self-embedding `iota_0`, since halving plus invariance gives zero. The answer is
negative and the reason is exact: the rank function is blind to the halving, because `R ~= R^2`.
What survives is a two-part route, recorded as Sections 4-5.

## 0. Notation

`R = L_(F_2)(1,2)`, `M` a rank ultraproduct over a field of characteristic two,
`sigma : EL_3(R) -> M^x` a homomorphism, `n_ab(r) = sigma(x_ab(r)) - 1`, `rho(a) = rk(n_12(a))`,
`rho = rho(1)`. For a finite word `gamma` over `{0,1}` put `e_gamma = s_gamma t_gamma` and

```text
a_gamma = n_12(e_gamma),  b_gamma = n_23(e_gamma),  P_gamma = b_gamma a_gamma,
delta_gamma = rk(P_gamma),   delta_sh = rk(n_23(s_0) n_12(t_0)).
```

In characteristic two `x_ab(c)^2 = 1`, so `n_ab(c)^2 = 0` and `sigma(x_ab(c))^-1 = 1 + n_ab(c)`.

## 1. The deviation identity at the shifted pair

Put `X = n_12(t_0)`, `Y = n_23(s_0)`. Since `t_0 s_0 = 1`, Corollary 1.1 of
`el3-two-root-self-similarity-2026-09-12.md` with `(a, b) = (t_0, s_0)` gives

```text
rk( n_13(1) - X Y ) = rk( Y X ) = delta_sh .
```

`rk(n_13(1)) = rho(1) = rho` by part 1 of `leavitt-rank-models-have-uniform-root-displacement`. So
subadditivity of rank in both directions gives

```text
| rk(X Y) - rho | <= delta_sh ,      rho <= delta_sh + rk(X Y) .
```

So the non-vanishing order `XY` is pinned to `rho` within `delta_sh`, and `delta_sh` is exactly the
deviation of `n_13(1)` from the reversed product. This is the bridge in exact form. It is **not** a
contradiction: it says the two orders differ by `delta_sh`, and is consistent with any
`delta_sh in [0, rho]`.

## 2. Displacement constancy: the halving is invisible

By part 4 of `leavitt-rank-models-have-uniform-root-displacement`, `rho(e) = rho` for **every**
nonzero idempotent `e` of `R`. In particular

```text
rho(e_gamma) = rho   for every word gamma,   and   rk(n_13(e_gamma)) = rho .
```

So the level-`k` corner root elements are displaced exactly as much as the unit ones, for every `k`.
The structural reason is `R ~= R^2`: every corner `e R` with `e != 0` is isomorphic to `R`, and
monomial pure infiniteness makes the rank function insensitive to passing to a corner. **So no
iteration of corner embeddings contracts root displacements, and a halving identity for `rho` is
false, not merely unavailable.** Any contraction must act on the product deviation while the
individual displacements stay constant.

## 3. Branch deviations depend only on the level

**Proposition.** For words `gamma`, `gamma'` with `|gamma| = |gamma'| = k`, `delta_gamma = delta_gamma'`.

*Proof.* Let `w = s_gamma t_gamma' + s_gamma' t_gamma + sum_{mu} s_mu t_mu`, the sum over the
remaining words `mu` of length `k`. Then `w^2 = sum_{|mu| = k} e_mu = 1`, so `w` is an involution and
a unit of `R`, and `W = diag(w, w, w)` lies in `GL_3(R) = EL_3(R)`
(`leavitt-gl-equals-el-and-perfect-unit-group`). Now `W x_ab(c) W^-1 = x_ab(w c w)` and
`w e_gamma w = e_gamma'`, so conjugation by `sigma(W)` carries `a_gamma` to `a_gamma'`, `b_gamma` to
`b_gamma'`, hence `P_gamma` to `P_gamma'`. Conjugation by a unit preserves rank. QED

This generalizes Proposition 2(4) of the self-similarity artifact from `k = 1` to every level, and it
makes `delta(k) := delta_gamma` (`|gamma| = k`) a well-defined function of the level alone.

## 4. The one contraction that would work, and why it is refuted

The Cuntz relation gives `1 = sum_{|gamma| = k} e_gamma`, so level `k` carries `2^k` branch products
`P_gamma`, all of the same rank `delta(k)` by Section 3. **If** their ranks were additive, that is

```text
sum_{|gamma| = k} rk(P_gamma) <= 1 ,
```

then `delta(k) <= 2^(-k) -> 0`, which with Section 5 would force `delta(0) = 0` and prove the gate.

Additivity is refuted. The branch defects `a_gamma`, `b_gamma` commute but need not have orthogonal
ranges: in the natural tensor square of `rank-modelled-coefficients-violate-two-root-identities` the
commuting branches act on tensor factors, where ranks do not add, and that model has
`rk(N_23 N_12) = 2/9` over `D = colim M_(2^k)(F_2)`. So corner data alone supplies no contraction,
and Proposition 2(5) of the self-similarity artifact remains an upper bound with no companion lower
bound.

## 5. What survives: a two-part route into the gate

By Section 3, `delta(k)` is well defined. The gate follows from the conjunction of two open claims:

* `leavitt-corner-deviations-are-level-independent`: `delta(k) = delta(0)` for every `k`;
* `leavitt-corner-deviations-vanish-along-levels`: `delta(k) -> 0`.

Together they give `delta(0) = 0`, hence `N_23 N_12 = 0` on the unit pair, hence triviality by
corner locality. Route: `two-root-identity-via-level-contraction`.

Level-independence is not automatic: Corollary 2.4 of the mechanism artifact records that the
shifted pair is **not** conjugate to the unit pair, so the conjugation of Section 3 does not cross
levels. Vanishing is not automatic either, by Section 4. Neither half is known.

## 6. Scope

Sections 1-3 are proved here. Section 4's refutation is quoted from the landed calibration and is
not re-derived. Section 2 uses parts 1 and 4 of the displacement claim as landed. Nothing here
decides the gate.
