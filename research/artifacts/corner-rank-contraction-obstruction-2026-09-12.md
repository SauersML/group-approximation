# Corner rank data cannot contract the two-root deviation

Lane `w3-gate-bridge-a`. Target: `N_23 N_12 = 0` for characteristic-two rank models of
`EL_3(L_(F_2)(1,2))`, equivalently (corner locality, Corollary 2.4 of
`two-root-identity-nonsofic-mechanism-2026-09-12.md`) `rk(n_23(s_0) n_12(t_0)) = 0`.

The directive was to look for a rank identity pushing that product into a corner whose rank
**halves** under the self-embedding `iota_0`, since halving plus invariance gives zero. The answer is
negative and the reason is exact: the rank function is blind to the halving, because `R ~= R^2`.
Section 3a (after `gk-vf-linear`, Section 56) shows the branch deviation is constant at every positive
level. Section 5 records that the level form of the gate is then a restatement of the binary gate,
not a reduction of it.

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

## 3a. Constancy at positive levels

This extension is due to `gk-vf-linear`, Section 56 of its verification artifact, and was re-derived
here. An earlier version of this artifact said the conjugation of Section 3 does not cross levels.
That is false for nonempty words.

**Proposition.** For nonempty words `gamma`, `gamma'` of any lengths, `delta_gamma = delta_gamma'`.
So `delta(k) = delta(1)` for every `k >= 1`.

*Proof.* Let `|gamma| = m >= 1`. Then `1 - e_gamma = sum_{i=1..m} S[c_i]T[c_i]`, where `c_i` agrees
with `gamma` before its `i`-th letter and differs there. Choose a complete prefix code
`d_1, ..., d_m`, for instance `d_i = 1^(i-1) 0` for `i < m` and `d_m = 1^(m-1)`, and put
`Z = sum_i S[c_i]T[d_i]`. Distinct words of a prefix code are incomparable, so
`T[c_j]S[c_i] = delta_ij = T[d_j]S[d_i]`. Hence

```text
Z*Z = sum_i e_(d_i) = 1,     ZZ* = 1 - e_gamma,     t_gamma Z = 0 = Z* s_gamma .
```

Build `Z'` likewise for `gamma'`, and put `w = s_gamma' t_gamma + Z'Z*` and `w' = s_gamma t_gamma' + ZZ'*`.
All cross products vanish, so `w w' = e_gamma' + Z'Z'* = 1`, `w' w = e_gamma + ZZ* = 1`, and
`w e_gamma w' = e_gamma'`. As in Section 3, `diag(w, w, w)` lies in `EL_3(R)`, and conjugation by its
image carries `P_gamma` to `P_gamma'`. QED

**What it cannot reach.** No unit carries `e_gamma` to `e_(empty) = 1`. So this compares every
positive level with level one, and never with `delta(0) = rk(N_23 N_12)`.

**Calibration.** Over `D = colim M_(2^k)(F_2)` there is no such unit, since `s_gamma' t_gamma` does not
lie in `D` when the lengths differ. In the tensor-square model of
`rank-modelled-coefficients-violate-two-root-identities`, `delta(k) = 2 . 4^(-k) / 9` is not constant.
So constancy across levels genuinely uses the Leavitt units.

## 4. The one contraction that would work, and why corner data do not supply it

The Cuntz relation gives `1 = sum_{|gamma| = k} e_gamma`, so level `k` carries `2^k` branch products
`P_gamma`, all of the same rank `delta(k) = delta(1)` by Sections 3-3a. **If** their ranks were
additive, that is

```text
sum_{|gamma| = k} rk(P_gamma) <= 1 ,
```

then `delta(1) <= 2^(-k)` for every `k`, so `delta(1) = 0`, and by Section 5 the model is trivial.

Corner data do not supply this inequality. The natural route to it would be orthogonality of the
root branch defects `a_gamma`, `b_gamma` for distinct words, and that orthogonality fails: in the
natural tensor square of `rank-modelled-coefficients-violate-two-root-identities` the commuting
branches act on tensor factors, and that model has `rk(N_23 N_12) = 2/9` over
`D = colim M_(2^k)(F_2)`.

**Correction (after `w3-vf-linear`, Section 16.1 of its verification artifact).** An earlier version
said additivity is *refuted*. That overstates. In the tensor-square model
`P_gamma = Y_gamma (x) X_gamma + X_gamma (x) Y_gamma` has image in independent blocks
`phi(e_gamma) V (x) phi(e_gamma) V`, so `sum_gamma rk(P_gamma) = 2^(1-k)/9 <= 1` and the calibration
**satisfies** the displayed inequality. It refutes only orthogonality of `a_gamma`, `b_gamma`. In a
Leavitt rank model the displayed inequality implies triviality of the model, so no calibration over
another ring can refute it; it is simply not available from corner data.

Proposition 2(5) of the self-similarity artifact remains an upper bound with no companion lower bound.

## 5. The level form is a restatement of the binary gate

By Section 3a, `delta(k) = delta(1) = rk(n_23(e_0) n_12(e_0))` for every `k >= 1`, while
`delta(0) = rk(N_23 N_12)` is the unit pair itself. By Lemma 2.3 of the mechanism artifact,
`(iota_0(x_12(1)), iota_0(x_23(1)))` is simultaneously conjugate to `(x_12(e_0), x_23(e_0))`. So corner
locality (`two-root-identity-is-corner-local-for-leavitt-rank-models`, condition 3 with `P = 0`) gives

```text
delta(1) = 0   iff   sigma is trivial   iff   delta(0) = 0 .
```

The two open claims therefore stand as follows (`gk-vf-linear`, Section 56):

* `leavitt-corner-deviations-vanish-along-levels`, `delta(k) -> 0`, is equivalent to `delta(1) = 0`.
  Quantified over all models, it is exactly: every characteristic-two rank model of
  `EL_3(L_(F_2)(1,2))` is trivial. It is the binary gate, not half of it.
* `leavitt-corner-deviations-are-level-independent`, `delta(k) = delta(0)`, reduces to
  `delta(1) = delta(0)` and follows from the vanishing claim.

The route `two-root-identity-via-level-contraction` now targets `non-linear-sofic-group`. It requires
this artifact's claim, the vanishing claim and corner locality, and is marked as a restatement. An
earlier version targeted `rank-models-of-el3-satisfy-the-two-root-identities`, the statement for every
simple characteristic-`p` algebra without a rank model. A binary-only argument overshoots that target.
The earlier version also required the redundant level-independence claim.

What remains is the gate itself, and Section 4 says what it cannot be proved by: corner data do not
supply additivity, and root displacements are constant. Neither route to vanishing is known.

## 6. Scope

Sections 1-3 are proved here. Section 3a is `gk-vf-linear`'s extension, re-derived here. Section 4
quotes from the landed calibration, without re-deriving it, the failure of orthogonality and the
level-`k` sum. Section 5 uses Lemma 2.3 of the mechanism artifact and corner locality as landed and
verified. Section 2 uses parts 1 and 4 of the displacement claim as landed. Nothing here decides the
gate.
